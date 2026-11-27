#!/usr/bin/env python3
"""
爆炒江湖 · 百味楼 & 厨神大赛 本地可视化助手后端服务
仅使用 Python 标准库（http.server），无需额外安装第三方依赖。
"""

import argparse
import glob
import json
import os
import threading
import traceback
import webbrowser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

from bcjh_solver import (
    BASE_DIR,
    BUNDLE_DIR,
    DATA_DIR,
    DATA_URL,
    RULE_URL,
    ARCHIVE_URL,
    SKILL_KEYS_LOW,
    SKILL_CN,
    GameContext,
    load_or_fetch,
    solve_rule,
)
from baiweilou_solver import BaiweilouSolver, describe_chef_buffs

WEB_DIR = os.path.join(BUNDLE_DIR, "web")
FLOORS_FILE = os.path.join(DATA_DIR, "baiweilou_floors.json")
BUNDLED_FLOORS_FILE = os.path.join(BUNDLE_DIR, "data", "baiweilou_floors.json")


def ensure_default_floors():
    os.makedirs(DATA_DIR, exist_ok=True)
    if not os.path.exists(FLOORS_FILE) and os.path.exists(BUNDLED_FLOORS_FILE):
        with open(BUNDLED_FLOORS_FILE, "r", encoding="utf-8") as src:
            content = src.read()
        with open(FLOORS_FILE, "w", encoding="utf-8") as dst:
            dst.write(content)


ensure_default_floors()


class AppState:
    def __init__(self):
        self.lock = threading.Lock()
        self.gd = load_or_fetch(os.path.join(DATA_DIR, "data.min.json"), DATA_URL)
        self.fg = load_or_fetch(os.path.join(DATA_DIR, "foodgod_rule.json"), RULE_URL)
        self.ctx_cache = {}

    def refresh_game_data(self):
        with self.lock:
            self.gd = load_or_fetch(os.path.join(DATA_DIR, "data.min.json"), DATA_URL, refresh=True)
            self.fg = load_or_fetch(os.path.join(DATA_DIR, "foodgod_rule.json"), RULE_URL, refresh=True)
            self.ctx_cache.clear()
        return {
            "recipes_total": len(self.gd.get("recipes", [])),
            "chefs_total": len(self.gd.get("chefs", [])),
            "rules_count": len(self.fg.get("rules", [])),
        }

    def list_saved_tokens(self):
        tokens = []
        for p in sorted(glob.glob(os.path.join(DATA_DIR, "user_*.json"))):
            bn = os.path.basename(p)
            tok = bn[len("user_") : -len(".json")]
            if tok:
                tokens.append(tok)
        return tokens

    def get_context(self, token, refresh=False):
        token = token.strip().upper()
        if not token:
            raise ValueError("校验码不能为空")
        with self.lock:
            if not refresh and token in self.ctx_cache:
                return self.ctx_cache[token]
            user_path = os.path.join(DATA_DIR, f"user_{token}.json")
            ua = load_or_fetch(user_path, ARCHIVE_URL.format(token=token), refresh=refresh)
            if ua.get("ret") != "S":
                if os.path.exists(user_path) and refresh:
                    os.remove(user_path)
                raise ValueError(f"拉取校验码 [{token}] 失败，请检查校验码是否正确或已过期：{ua.get('msg', ua)}")
            ctx = GameContext(self.gd, ua)
            self.ctx_cache[token] = ctx
            return ctx

    def account_summary(self, token, refresh=False):
        ctx = self.get_context(token, refresh=refresh)
        return {
            "token": token.strip().upper(),
            "chefs_got": len(ctx.owned_chefs),
            "chefs_ult": sum(1 for c in ctx.owned_chefs if c["ult"]),
            "recipes_got": len(ctx.owned_recipes),
            "recipes_ex": sum(1 for r in ctx.owned_recipes if r["ex"]),
            "deco_buff": ctx.deco_buff,
            "ulti": ctx.ulti,
            "known_equips": len(ctx.known_equip_ids),
        }

    def load_floors(self):
        if not os.path.exists(FLOORS_FILE):
            return []
        with open(FLOORS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)

    def save_floors(self, floors):
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(FLOORS_FILE, "w", encoding="utf-8") as f:
            json.dump(floors, f, ensure_ascii=False, indent=2)

    def format_baiweilou(self, score, target, res):
        cids, eids, pool, det, sts = res
        chefs_out = []
        for idx, st in enumerate(sts, 1):
            ch = st["chef"]
            chefs_out.append({
                "pos": idx,
                "id": ch["id"],
                "name": ch["name"],
                "rarity": ch["rarity"],
                "equip": st["equip"]["name"] if st["equip"] else "无",
                "skills_desc": describe_chef_buffs(st),
            })
        return {
            "score": score,
            "target": target,
            "passed": score >= target,
            "pool": {SKILL_CN[k]: int(pool[k]) for k in SKILL_KEYS_LOW},
            "chefs": chefs_out,
            "dishes": [
                {
                    "recipe": d["recipe"],
                    "rarity": d["rarity"],
                    "grade": d["grade"],
                    "ratio": round(d["ratio"], 1),
                    "base": d["base"],
                    "basic_pct": round(d["basic_pct"]),
                    "total_buff": round(d["total_buff"]),
                    "score": d["score"],
                }
                for d in det
            ],
        }


STATE = AppState()


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=WEB_DIR, **kwargs)

    def log_message(self, format, *args):
        pass  # Keep console clean

    def send_json(self, obj, code=200):
        raw = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def read_json_body(self):
        ln = int(self.headers.get("Content-Length", "0") or "0")
        if ln <= 0:
            return {}
        return json.loads(self.rfile.read(ln).decode("utf-8"))

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/api/init":
            rules_brief = [
                {
                    "id": r["Id"],
                    "title": r["Title"],
                    "message": r.get("message", ""),
                    "pass_line": r.get("PassLine") or [],
                    "start_time": r.get("start_time", ""),
                    "end_time": r.get("end_time", ""),
                }
                for r in STATE.fg.get("rules", [])
            ]
            recipe_names = [
                {"name": r["name"], "rarity": r["rarity"], "price": r["price"]}
                for r in STATE.gd.get("recipes", [])
            ]
            self.send_json({
                "ok": True,
                "tokens": STATE.list_saved_tokens(),
                "floors": STATE.load_floors(),
                "rules": rules_brief,
                "recipes": recipe_names,
            })
            return
        return super().do_GET()

    def do_POST(self):
        parsed = urlparse(self.path)
        try:
            body = self.read_json_body()

            if parsed.path == "/api/refresh_data":
                info = STATE.refresh_game_data()
                rules_brief = [
                    {
                        "id": r["Id"],
                        "title": r["Title"],
                        "message": r.get("message", ""),
                        "pass_line": r.get("PassLine") or [],
                        "start_time": r.get("start_time", ""),
                        "end_time": r.get("end_time", ""),
                    }
                    for r in STATE.fg.get("rules", [])
                ]
                self.send_json({"ok": True, "info": info, "rules": rules_brief})
                return

            if parsed.path == "/api/account":
                token = body.get("token", "")
                refresh = bool(body.get("refresh", False))
                summary = STATE.account_summary(token, refresh=refresh)
                self.send_json({"ok": True, "account": summary, "tokens": STATE.list_saved_tokens()})
                return

            if parsed.path == "/api/floors/save":
                floor = body.get("floor") or {}
                name = str(floor.get("name", "")).strip()
                slots = int(floor.get("slots", 3))
                target = int(floor.get("target", 0))
                dishes = [d.strip() for d in floor.get("dishes", []) if str(d).strip()]
                if not name or not dishes:
                    raise ValueError("楼层名称和菜谱不能为空")
                # Validate all dish names exist
                valid_names = {r["name"] for r in STATE.gd.get("recipes", [])}
                bad = [d for d in dishes if d not in valid_names]
                if bad:
                    raise ValueError(f"图鉴中找不到以下菜谱：{', '.join(bad)}")
                floors = STATE.load_floors()
                fid = floor.get("id")
                if fid is not None:
                    updated = False
                    for i, fl in enumerate(floors):
                        if fl.get("id") == fid:
                            floors[i] = {"id": fid, "name": name, "slots": slots, "target": target, "dishes": dishes}
                            updated = True
                            break
                    if not updated:
                        floors.append({"id": fid, "name": name, "slots": slots, "target": target, "dishes": dishes})
                else:
                    next_id = max((fl.get("id", 0) for fl in floors), default=0) + 1
                    floors.append({"id": next_id, "name": name, "slots": slots, "target": target, "dishes": dishes})
                STATE.save_floors(floors)
                self.send_json({"ok": True, "floors": floors})
                return

            if parsed.path == "/api/floors/delete":
                fid = body.get("id")
                floors = [fl for fl in STATE.load_floors() if fl.get("id") != fid]
                STATE.save_floors(floors)
                self.send_json({"ok": True, "floors": floors})
                return

            if parsed.path == "/api/solve/baiweilou":
                token = body.get("token", "")
                dishes_in = body.get("dishes", [])
                slots = int(body.get("slots", 3))
                target = int(body.get("target", 0))
                swap_equips = bool(body.get("swap_equips", False))
                exclude_names = [x.strip() for x in body.get("exclude", []) if str(x).strip()]

                ctx = STATE.get_context(token)
                solver = BaiweilouSolver(ctx)
                dishes = solver.resolve_dishes(dishes_in)
                by_name = {c["name"]: c["id"] for c in ctx.chefs_by_id.values()}
                ex_ids = {by_name[nm] for nm in exclude_names if nm in by_name}

                sc_no, res_no = solver.solve(dishes, slots=slots, target=target, swap_equips=False, exclude_ids=ex_ids)
                out = {"no_swap": STATE.format_baiweilou(sc_no, target, res_no)}
                if swap_equips:
                    sc_sw, res_sw = solver.solve(dishes, slots=slots, target=target, swap_equips=True, exclude_ids=ex_ids)
                    out["with_swap"] = STATE.format_baiweilou(sc_sw, target, res_sw)
                self.send_json({"ok": True, "result": out})
                return

            if parsed.path == "/api/solve/baiweilou_all":
                token = body.get("token", "")
                swap_equips = bool(body.get("swap_equips", False))
                ctx = STATE.get_context(token)
                solver = BaiweilouSolver(ctx)
                floors = STATE.load_floors()
                results = []
                total_no_swap = 0
                for fl in floors:
                    dishes = solver.resolve_dishes(fl["dishes"])
                    sc, res = solver.solve(dishes, slots=fl["slots"], target=fl["target"], swap_equips=swap_equips)
                    formatted = STATE.format_baiweilou(sc, fl["target"], res)
                    total_no_swap += sc
                    results.append({
                        "id": fl["id"],
                        "name": fl["name"],
                        "slots": fl["slots"],
                        "result": formatted,
                    })
                self.send_json({"ok": True, "total_score": total_no_swap, "floors": results})
                return

            if parsed.path == "/api/solve/foodgod":
                token = body.get("token", "")
                rule_id = int(body.get("rule_id", 1))
                swap_equips = bool(body.get("swap_equips", False))
                ctx = STATE.get_context(token)
                rules_by_id = {r["Id"]: r for r in STATE.fg.get("rules", [])}
                rule = rules_by_id.get(rule_id)
                if not rule:
                    raise ValueError(f"未找到规则 ID={rule_id}")
                score, state, details = solve_rule(ctx, rule, swap_equips=swap_equips, restarts=10, iters=1800)
                pass_line = rule.get("PassLine") or []
                tier = ""
                if len(pass_line) == 3:
                    if score >= pass_line[0]:
                        tier = f"稳过高保 ({pass_line[0]:,})"
                    elif score >= pass_line[1]:
                        tier = f"过中保 ({pass_line[1]:,})"
                    elif score >= pass_line[2]:
                        tier = f"过低保 ({pass_line[2]:,})"
                    else:
                        tier = f"未达低保 ({pass_line[2]:,})"
                elif len(pass_line) == 1:
                    tier = f"{'已过线' if score >= pass_line[0] else '未过线'} (目标 {pass_line[0]:,})"

                by_pos = {0: [], 1: [], 2: []}
                for d in details:
                    by_pos[d["pos"]].append(d)
                groups = []
                for p in range(3):
                    items = by_pos[p]
                    if not items:
                        continue
                    groups.append({
                        "pos": p + 1,
                        "chef": items[0]["chef"],
                        "equip": items[0]["equip"],
                        "subtotal": sum(x["score"] for x in items),
                        "dishes": items,
                    })
                self.send_json({
                    "ok": True,
                    "result": {
                        "rule_title": rule["Title"],
                        "message": rule.get("message", ""),
                        "score": score,
                        "tier": tier,
                        "pass_line": pass_line,
                        "groups": groups,
                    },
                })
                return

            self.send_json({"ok": False, "error": f"Unknown API: {parsed.path}"}, code=404)
        except Exception as e:
            traceback.print_exc()
            self.send_json({"ok": False, "error": str(e)}, code=400)


def main():
    parser = argparse.ArgumentParser(description="爆炒江湖本地配队助手 Web 服务")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--no-browser", action="store_true")
    args = parser.parse_args()

    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    url = f"http://127.0.0.1:{args.port}/"
    print(f"爆炒江湖配队助手已启动: {url}")
    print("按 Ctrl+C 关闭服务。")
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n服务已关闭。")
        server.server_close()


if __name__ == "__main__":
    main()
