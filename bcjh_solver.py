#!/usr/bin/env python3
"""
爆炒江湖（白菜菊花体系）本地自动配队与跑分求解器
支持：
- 通过白菜菊花校验码自动拉取个人存档（厨师/修炼/厨具/遗玉/心法盘/菜谱/专精）
- 100% 对齐 h5.baochaojianghu.com (calculator.js) 算分规则
- 自动求解每周厨神大赛（御前/皇城等分段）及周年/限时活动挑战关
- 可扩展自定义规则（如百味楼）
"""

import argparse
import json
import math
import os
import random
import ssl
import sys
import urllib.request
from copy import deepcopy
from collections import defaultdict

if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(sys.executable)
    BUNDLE_DIR = getattr(sys, "_MEIPASS", BASE_DIR)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
    BUNDLE_DIR = BASE_DIR
DATA_DIR = os.path.join(BASE_DIR, "data")

DATA_URL = "https://h5.baochaojianghu.com/data/data.min.json"
RULE_URL = "https://i.baochaojianghu.com/api/get_rule"
ARCHIVE_URL = "https://yx518.com/api/archive.do?token={token}"

SKILL_KEYS_CAP = ["Stirfry", "Boil", "Knife", "Fry", "Bake", "Steam"]
SKILL_KEYS_LOW = ["stirfry", "boil", "knife", "fry", "bake", "steam"]
SKILL_CN = {"stirfry": "炒", "boil": "煮", "knife": "切", "fry": "炸", "bake": "烤", "steam": "蒸"}
PER_SKILL_ORDER = ["stirfry", "fry", "bake", "steam", "boil", "knife"]
CONDIMENT_TYPES = {"Sweet", "Sour", "Spicy", "Salty", "Bitter", "Tasty"}
CONDIMENT_CN = {"Sweet": "甜", "Sour": "酸", "Spicy": "辣", "Salty": "咸", "Bitter": "苦", "Tasty": "鲜"}
MATERIAL_TYPES = {"Meat", "Vegetable", "Creation", "Fish"}
GRADE_BUFF = {1: 0, 2: 10, 3: 30, 4: 50, 5: 100}
GRADE_CN = {0: "不足", 1: "可", 2: "优", 3: "特", 4: "神", 5: "传"}
LIMIT_BY_RARITY = [0, 40, 30, 25, 20, 15]

ORIGIN_TO_MTYPE = {
    "菜棚": "vegetable", "菜地": "vegetable", "森林": "vegetable",
    "鸡舍": "meat", "猪圈": "meat", "牧场": "meat",
    "作坊": "creation",
    "池塘": "fish",
}


def download_file(url, dest):
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    ctx = ssl.create_default_context()
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=25, context=ctx) as resp:
        raw = resp.read()
    with open(dest, "wb") as f:
        f.write(raw)
    return raw


def load_or_fetch(path, url, refresh=False):
    if refresh or not os.path.exists(path):
        download_file(url, path)
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def judge_eff(eff):
    t = eff.get("type", "")
    return (
        t.startswith("Use")
        or t == "Gold_Gain"
        or t.endswith("Price")
        or t.endswith("Limit")
        or t.startswith("BasicPrice")
        or t == "MaterialReduce"
    )


class GameContext:
    def __init__(self, game_data, user_archive):
        self.gd = game_data
        self.user_msg = user_archive.get("msg", user_archive)

        self.skills_by_id = {s["skillId"]: s for s in game_data["skills"]}
        self.materials_by_id = {m["materialId"]: m for m in game_data["materials"]}
        self.disks_by_id = {d["diskId"]: d for d in game_data["disks"]}

        # Amber suits
        self.amber_suits = {}
        for suit in game_data.get("amberSuits", []):
            slist = [self.skills_by_id[sid] for sid in suit.get("skill", []) if sid in self.skills_by_id]
            effs = []
            for sk in slist:
                effs.extend(sk.get("effect", []))
            self.amber_suits[suit["suitId"]] = {
                "suitId": suit["suitId"],
                "name": suit["name"],
                "requireNum": suit["requireNum"],
                "effects": effs,
            }

        # Ambers
        self.ambers_by_id = {}
        for amb in game_data.get("ambers", []):
            slist = [self.skills_by_id[sid] for sid in amb.get("skill", []) if sid in self.skills_by_id]
            a = dict(amb)
            a["itemType"] = amb.get("itemType") or 67
            a["amberSuitId"] = amb.get("amberSuitId") or 0
            a["skill_list"] = slist
            self.ambers_by_id[amb["amberId"]] = a

        # Equips
        self.equips_by_id = {}
        for eq in game_data.get("equips", []):
            effs = []
            descs = []
            for sid in eq.get("skill", []):
                if sid in self.skills_by_id:
                    effs.extend(self.skills_by_id[sid].get("effect", []))
                    descs.append(self.skills_by_id[sid].get("desc", ""))
            e = dict(eq)
            e["effect"] = effs
            e["skill_desc"] = "；".join(descs)
            self.equips_by_id[eq["equipId"]] = e

        # Parse user archive
        self.rep_got = {}
        self.rep_ex = {}
        for r in self.user_msg.get("recipes", []):
            rid = r["id"]
            self.rep_got[rid] = (r.get("got") == "是")
            self.rep_ex[rid] = (r.get("ex") == "是")

        self.chef_got = {}
        self.chef_ult = {}
        self.chef_equip = {}
        self.chef_ambers = {}
        self.chef_dlv = {}
        for c in self.user_msg.get("chefs", []):
            cid = c["id"]
            self.chef_got[cid] = (c.get("got") == "是")
            self.chef_ult[cid] = (c.get("ult") == "是")
            if c.get("equip"):
                self.chef_equip[cid] = c["equip"]
            if c.get("ambers"):
                self.chef_ambers[cid] = c["ambers"]
            if c.get("dlv"):
                self.chef_dlv[cid] = c["dlv"]

        self.deco_buff = self.user_msg.get("decorationEffect", 0) or 0

        # Parse recipes
        self.recipes_by_id = {}
        self.owned_recipes = []
        for item in game_data["recipes"]:
            r = dict(item)
            rid = item["recipeId"]
            r["id"] = rid
            skills = {}
            for k in SKILL_KEYS_LOW:
                if item.get(k):
                    skills[k] = item[k]
            r["skills"] = skills
            mtypes = set()
            for m in item.get("materials", []):
                mat = self.materials_by_id.get(m["material"])
                if mat:
                    mt = ORIGIN_TO_MTYPE.get(mat.get("origin"))
                    if mt:
                        mtypes.add(mt)
            r["materials_type"] = mtypes
            r["tags"] = set(item.get("tags") or [])
            r["got"] = self.rep_got.get(rid, False)
            r["ex"] = self.rep_ex.get(rid, False)
            self.recipes_by_id[rid] = r
            if r["got"]:
                self.owned_recipes.append(r)

        # Parse chefs & compute global ultimate bonuses (matching index.js setUlti)
        self.ulti = {
            "decoBuff": self.deco_buff,
            "Stirfry": 0, "Boil": 0, "Knife": 0, "Fry": 0, "Bake": 0, "Steam": 0,
            "Male": 0, "Female": 0, "All": 0,
            "PriceBuff_1": 0, "PriceBuff_2": 0, "PriceBuff_3": 0, "PriceBuff_4": 0, "PriceBuff_5": 0,
            "MaxLimit_1": 0, "MaxLimit_2": 0, "MaxLimit_3": 0, "MaxLimit_4": 0, "MaxLimit_5": 0,
        }
        self.ult_unlocked_uids = set()
        self.qixia_skill_by_tag = defaultdict(lambda: {k: 0 for k in SKILL_KEYS_CAP})

        # Map baseChefId -> list of chefIds for qixia check
        base_to_chefs = defaultdict(list)
        for ch in game_data["chefs"]:
            if ch.get("baseChefId") is not None:
                base_to_chefs[ch["baseChefId"]].append(ch["chefId"])

        self.chefs_by_id = {}
        self.owned_chefs = []

        for item in game_data["chefs"]:
            cid = item["chefId"]
            c = dict(item)
            c["id"] = cid
            c["tags"] = set(item.get("tags") or [])
            c["skills"] = {k: (item.get(k) or 0) for k in SKILL_KEYS_LOW}
            base_sk = self.skills_by_id.get(item.get("skill"))
            c["skill_effect"] = base_sk.get("effect", []) if base_sk else []
            c["skill_desc"] = base_sk.get("desc", "") if base_sk else ""

            ult_list = []
            for sid in item.get("ultimateSkillList", []):
                sk = self.skills_by_id.get(sid)
                if sk:
                    uid = f"{cid},{sid}"
                    ult_list.append((uid, sk))
            c["ultimate_list"] = ult_list
            c["got"] = self.chef_got.get(cid, False)
            c["ult"] = self.chef_ult.get(cid, False)
            c["default_equip"] = self.chef_equip.get(cid, 0)
            c["default_ambers"] = self.chef_ambers.get(cid, [])
            c["default_dlv"] = self.chef_dlv.get(cid, 1)

            self.chefs_by_id[cid] = c
            if c["got"]:
                self.owned_chefs.append(c)

            # Global ult contributions (matching setUlti)
            if c["ult"]:
                for uid, sk in ult_list:
                    cond = sk.get("skillCondition")
                    if cond in ("Partial", "Next"):
                        self.ult_unlocked_uids.add(uid)
                    if cond == "Self":
                        effs = [e for e in sk.get("effect", []) if e.get("type") not in ("Material_Gain", "GuestDropCount")]
                        if effs:
                            self.ult_unlocked_uids.add(uid)
                    if not sk.get("isGlobalQuanJiFa") and not sk.get("isQiXiaJiFa"):
                        for eff in sk.get("effect", []):
                            if eff.get("condition") == "Global" and not eff.get("tag") and eff.get("type") in SKILL_KEYS_CAP:
                                self.ulti[eff["type"]] += eff["value"]
                            rty = eff.get("rarity")
                            if rty in (1, 2, 3, 4, 5):
                                if eff.get("type") == "UseAll":
                                    self.ulti[f"PriceBuff_{rty}"] += eff["value"]
                                if eff.get("type") == "MaxEquipLimit" and eff.get("condition") == "Global":
                                    self.ulti[f"MaxLimit_{rty}"] += eff["value"]
                    if sk.get("isGlobalQuanJiFa"):
                        eff = sk["effect"][0]
                        tag = eff.get("tag")
                        if tag == 1:
                            self.ulti["Male"] += eff["value"]
                        elif tag == 2:
                            self.ulti["Female"] += eff["value"]
                        else:
                            self.ulti["All"] += eff["value"]
                    if sk.get("isQiXiaJiFa"):
                        eff0 = sk["effect"][0]
                        cvl = eff0.get("conditionValueList", [])
                        match_cnt = 0
                        for cv in cvl:
                            for mcid in base_to_chefs.get(cv, []):
                                if self.chef_got.get(mcid):
                                    match_cnt += 1
                        if match_cnt >= len(cvl):
                            tag = eff0.get("tag")
                            for eff in sk["effect"]:
                                if eff.get("type") in SKILL_KEYS_CAP:
                                    self.qixia_skill_by_tag[tag][eff["type"]] += eff["value"]

        # Known owned equips pool (from currently equipped equips across all chefs)
        self.known_equip_ids = sorted(set(self.chef_equip.values()))

    def get_amber_suit_effects(self, ambers):
        suit_cnt = defaultdict(int)
        for amb in ambers:
            if amb and amb.get("itemType") == 88 and amb.get("amberSuitId"):
                suit_cnt[amb["amberSuitId"]] += 1
        effs = []
        for sid, suit in self.amber_suits.items():
            if suit_cnt.get(sid, 0) >= suit["requireNum"]:
                effs.extend(suit["effects"])
        return effs

    def get_chef_disk_sources(self, chef, eqp, ambers, rule):
        sources = list(chef["skill_effect"])
        for uid, sk in chef["ultimate_list"]:
            if uid in self.ult_unlocked_uids:
                sources.extend(sk.get("effect", []))
        if eqp and not rule.get("DisableEquipSkillEffect"):
            sources.extend(eqp["effect"])
        sources.extend(self.get_amber_suit_effects(ambers))
        return sources

    @staticmethod
    def disk_level_bonus(sources, conds):
        b = 0
        for e in sources:
            if e.get("type") == "AmberDiskLevel" and e.get("cal") == "Abs" and e.get("condition") in conds:
                b += e.get("value", 0)
        return b

    def build_lineup_state(self, chef_ids, equip_ids, rule):
        """
        Compute effective stats & skill effects for a 3-chef lineup (ordered pos 0, 1, 2).
        Matches calculator.js showChef() exactly.
        """
        n = len(chef_ids)
        chefs = [self.chefs_by_id[cid] for cid in chef_ids]
        equips = [self.equips_by_id.get(eid) if eid else None for eid in equip_ids]
        ambers_list = []
        for ch in chefs:
            ambs = []
            disk = self.disks_by_id.get(ch.get("disk"))
            slot_types = list(disk["info"]) + [0] if disk else [0]
            raw_ambs = ch.get("default_ambers") or []
            for idx, aid in enumerate(raw_ambs):
                if idx >= len(slot_types) or not aid:
                    continue
                amb = self.ambers_by_id.get(aid)
                if amb:
                    st = slot_types[idx]
                    if st == 0 or amb.get("type") == 4 or amb.get("type") == st:
                        ambs.append(amb)
            ambers_list.append(ambs)

        # Precompute disk sources for aura disk level bonus
        disk_sources = [self.get_chef_disk_sources(chefs[i], equips[i], ambers_list[i], rule) for i in range(n)]

        states = []
        for pos in range(n):
            ch = chefs[pos]
            eqp = equips[pos]
            ambs = ambers_list[pos]
            last_ch = chefs[pos - 1] if pos > 0 else None

            # Effective disk level
            base_dlv = ch.get("default_dlv", 1)
            dlv_bonus = self.disk_level_bonus(disk_sources[pos], {"Self"})
            prev_idx = pos - 1 if pos > 0 else None
            for k in range(n):
                conds = {"Partial", "Next"} if k == prev_idx else {"Partial"}
                dlv_bonus += self.disk_level_bonus(disk_sources[k], conds)
            eff_dlv = base_dlv + dlv_bonus

            equip_effect = []
            if eqp and not rule.get("DisableEquipSkillEffect"):
                equip_effect = [e for e in eqp["effect"] if judge_eff(e)]

            ambers_all_eff = []
            amber_price_eff = []
            for amb in ambs:
                amp = amb.get("amplification", 0)
                for sk in amb["skill_list"]:
                    for e in sk.get("effect", []):
                        ec = dict(e)
                        ec["value"] = ec.get("value", 0) + (eff_dlv - 1) * amp
                        ambers_all_eff.append(ec)
                        if judge_eff(ec):
                            amber_price_eff.append(ec)

            suit_effs = [e for e in self.get_amber_suit_effects(ambs) if judge_eff(e)]

            sum_skill_effect = []
            for e in ch["skill_effect"]:
                if e.get("condition") != "Next" and judge_eff(e):
                    sum_skill_effect.append(e)
            if last_ch:
                for e in last_ch["skill_effect"]:
                    if e.get("condition") == "Next" and judge_eff(e):
                        sum_skill_effect.append(e)
                for uid, sk in last_ch["ultimate_list"]:
                    if uid in self.ult_unlocked_uids:
                        for e in sk.get("effect", []):
                            if e.get("condition") == "Next" and judge_eff(e):
                                sum_skill_effect.append(e)
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if e.get("condition") == "Next":
                            continue
                        if judge_eff(e):
                            sum_skill_effect.append(e)
            sum_skill_effect.extend(suit_effs)

            # MutiEquipmentSkill
            muti_eq = 0
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if e.get("type") == "MutiEquipmentSkill" and e.get("cal") == "Percent":
                            muti_eq += e.get("value", 0)

            # Compute 6 skills
            skills_last = {}
            for key_cap, key_low in zip(SKILL_KEYS_CAP, SKILL_KEYS_LOW):
                val = self.ulti["All"] + self.ulti[key_cap]
                pct = 0
                if 1 in ch["tags"]:
                    val += self.ulti["Male"]
                if 2 in ch["tags"]:
                    val += self.ulti["Female"]
                for e in ch["skill_effect"]:
                    if e.get("type") == key_cap:
                        if e.get("cal") == "Abs":
                            val += e["value"]
                        elif e.get("cal") == "Percent":
                            pct += e["value"]
                for tag in ch["tags"]:
                    if tag in self.qixia_skill_by_tag:
                        val += self.qixia_skill_by_tag[tag][key_cap]
                for uid, sk in ch["ultimate_list"]:
                    if uid in self.ult_unlocked_uids:
                        for e in sk.get("effect", []):
                            if e.get("type") == key_cap and e.get("condition") == "Self":
                                if e.get("cal") == "Abs":
                                    val += e["value"]
                                elif e.get("cal") == "Percent":
                                    pct += e["value"]
                # Partial from all onsite chefs
                for k in range(n):
                    cur_ch = chefs[k]
                    for uid, sk in cur_ch["ultimate_list"]:
                        if uid in self.ult_unlocked_uids:
                            for e in sk.get("effect", []):
                                if e.get("type") == key_cap and e.get("condition") == "Partial":
                                    if e.get("conditionType") == "ChefTag":
                                        ok = bool(set(e.get("conditionValueList", [])) & ch["tags"])
                                    else:
                                        ok = True
                                    if ok:
                                        if e.get("cal") == "Abs":
                                            val += e["value"]
                                        elif e.get("cal") == "Percent":
                                            pct += e["value"]
                # Next from last_ch
                if last_ch:
                    for uid, sk in last_ch["ultimate_list"]:
                        if uid in self.ult_unlocked_uids:
                            for e in sk.get("effect", []):
                                if e.get("type") == key_cap and e.get("condition") == "Next":
                                    if e.get("cal") == "Abs":
                                        val += e["value"]
                                    elif e.get("cal") == "Percent":
                                        pct += e["value"]
                # Equip
                if eqp and not rule.get("DisableEquipSkillEffect"):
                    for e in eqp["effect"]:
                        if e.get("type") == key_cap:
                            if e.get("cal") == "Abs":
                                val += e["value"] * (100 + muti_eq) / 100
                            elif e.get("cal") == "Percent":
                                pct += e["value"] * (100 + muti_eq) / 100
                # Ambers
                for e in ambers_all_eff:
                    if e.get("type") == key_cap:
                        if e.get("cal") == "Abs":
                            val += e["value"]
                        elif e.get("cal") == "Percent":
                            pct += e["value"]
                base_sk_val = ch["skills"][key_low]
                val += math.ceil((base_sk_val + val) * pct / 100)
                skills_last[key_low] = base_sk_val + val

            states.append({
                "chef": ch,
                "equip": eqp,
                "ambers": ambs,
                "skills_last": skills_last,
                "sum_skill_effect": sum_skill_effect,
                "equip_effect": equip_effect,
                "amber_effect": amber_price_eff,
                "muti_eq": muti_eq,
            })

        # Precompute materialReduce & MaxEquipLimit partial auras across the 3 chefs
        partial_mat_reduce = []
        partial_limit_effs = []
        for st in states:
            ch = st["chef"]
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if e.get("type") == "MaterialReduce" and e.get("condition") == "Partial":
                            partial_mat_reduce.append((set(e.get("conditionValueList", [])), e["value"]))
                        if e.get("type") == "MaxEquipLimit" and e.get("condition") == "Partial":
                            partial_limit_effs.append(e)

        for st in states:
            # materialReduce for this chef
            mr = list(partial_mat_reduce)
            for e in st["sum_skill_effect"]:
                if e.get("type") == "MaterialReduce" and e.get("condition") == "Self":
                    mr.append((set(e.get("conditionValueList", [])), e["value"]))
            st["material_reduce"] = mr
            st["partial_limit_effs"] = partial_limit_effs

        return states

    @staticmethod
    def get_grade(skills_last, rep, rule):
        if rule.get("DisableCookbookRank"):
            gmax = 1
        else:
            gmax = 5
        mn = gmax
        for sk, req in rep["skills"].items():
            if req <= 0:
                continue
            sv = skills_last.get(sk, 0)
            if sv < req:
                return 0
            multi = int(sv // req)
            if multi < mn:
                mn = multi
        return mn

    def evaluate_lineup(self, chef_ids, equip_ids, recipe_groups, rule, counts=None, use_real_ex=True):
        """
        Evaluate a full 3-chef lineup with assigned recipes (list of 3 lists of up to 3 recipe IDs).
        If counts is None, automatically solves optimal counts respecting MaterialsLimit & limit caps.
        Returns (total_score, detail_dict).
        """
        states = self.build_lineup_state(chef_ids, equip_ids, rule)
        n = len(states)
        rec_eff_map = rule.get("RecipeEffect") or {}
        chef_tag_eff = rule.get("ChefTagEffect") or {}
        disable_multi = bool(rule.get("DisableMultiCookbook"))
        mat_limit_raw = rule.get("MaterialsLimit")

        # Build flat list of slots: (pos, slot_idx, rep)
        reps_by_pos = [[self.recipes_by_id[rid] for rid in recipe_groups[p]] for p in range(n)]

        # First compute grades and per-dish max_limit (without shared material limit)
        grades_by_pos = []
        for p in range(n):
            glist = [self.get_grade(states[p]["skills_last"], r, rule) for r in reps_by_pos[p]]
            grades_by_pos.append(glist)

        # Helper counters for PerRank / SameSkill / PerSkill
        def get_per_rank_cnt(pos, cond_val):
            return sum(1 for g in grades_by_pos[pos] if g >= cond_val)

        def get_same_skill_flag(pos):
            if len(reps_by_pos[pos]) < 3:
                return 0
            cnt = 0
            for sk in SKILL_KEYS_LOW:
                if all(sk in r["skills"] for r in reps_by_pos[pos]):
                    cnt += 1
            return cnt

        def get_per_skill_cnt_all(cond_val):
            sk = PER_SKILL_ORDER[cond_val - 1]
            return sum(1 for p in range(n) for r in reps_by_pos[p] if sk in r["skills"])

        def get_per_skill_cnt_pos(pos, cond_val):
            sk = PER_SKILL_ORDER[cond_val - 1]
            return sum(1 for r in reps_by_pos[pos] if sk in r["skills"])

        # Collect on-site Partial effects from all 3 chefs (matching calculator.js calScore two-pass logic)
        on_site_effects = []
        if not rule.get("DisableChefSkillEffect"):
            for p in range(n):
                st = states[p]
                for e in st["sum_skill_effect"]:
                    if e.get("condition") != "Partial":
                        continue
                    ct = e.get("conditionType")
                    if not ct:
                        ec = dict(e)
                        ec.pop("condition", None)
                        on_site_effects.append(ec)
                    elif ct == "PerRank":
                        ec = dict(e)
                        ec.pop("conditionType", None)
                        ec.pop("condition", None)
                        ec["value"] = e["value"] * get_per_rank_cnt(p, e["conditionValue"])
                        on_site_effects.append(ec)
                    elif ct == "SameSkill":
                        sf = get_same_skill_flag(p)
                        if sf > 0:
                            ec = dict(e)
                            ec.pop("conditionType", None)
                            ec.pop("condition", None)
                            ec["value"] = e["value"] * sf
                            on_site_effects.append(ec)
                    elif ct == "PerSkill":
                        ec = dict(e)
                        ec.pop("conditionType", None)
                        ec.pop("condition", None)
                        ec["value"] = e["value"] * get_per_skill_cnt_all(e["conditionValue"])
                        on_site_effects.append(ec)
                    elif ct in ("Rank", "CookbookRarity", "ChefTag", "CookbookTag", "CookbookTagOnce"):
                        ec = dict(e)
                        ec.pop("condition", None)
                        on_site_effects.append(ec)

        def eff_without_cond(eff, rep, st, eqp_flag=0, basic_flag=0):
            et = eff.get("type", "")
            muti = (100 + st["muti_eq"]) / 100.0 if eqp_flag else 1.0
            val = eff.get("value", 0) * muti
            if eff.get("condition") == "Partial":
                return 0
            if et.startswith("Use"):
                sub = et[3:]
                if sub in SKILL_KEYS_CAP and sub.lower() in rep["skills"]:
                    return val
                if sub in MATERIAL_TYPES and sub.lower() in rep["materials_type"]:
                    return val
                if sub in CONDIMENT_TYPES and rep.get("condiment") == sub:
                    return val
            elif et == "CookbookPrice":
                return val
            elif et == "BasicPrice" and basic_flag == 1:
                return val
            return 0

        def eval_effect(eff, rep, st, rep_cnt, grade, pos, eqp_flag=0, basic_flag=0):
            if eff.get("condition") == "Partial":
                return 0
            ct = eff.get("conditionType")
            if not ct:
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag)
            elif ct == "ExcessCookbookNum":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if rep_cnt >= eff["conditionValue"] else 0
            elif ct == "FewerCookbookNum":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if rep_cnt <= eff["conditionValue"] else 0
            elif ct == "PerRank":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) * get_per_rank_cnt(pos, eff["conditionValue"])
            elif ct == "Rank":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if grade >= eff["conditionValue"] else 0
            elif ct == "SameSkill":
                sf = get_same_skill_flag(pos)
                return eff["value"] * sf if sf > 0 else 0
            elif ct == "CookbookRarity":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if rep["rarity"] in eff.get("conditionValueList", []) else 0
            elif ct == "ChefTag":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if bool(set(eff.get("conditionValueList", [])) & st["chef"]["tags"]) else 0
            elif ct == "CookbookTag":
                mc = len(set(eff.get("conditionValueList", [])) & rep["tags"])
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) * mc if mc > 0 else 0
            elif ct == "CookbookTagOnce":
                mc = len(set(eff.get("conditionValueList", [])) & rep["tags"])
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) if mc > 0 else 0
            elif ct == "PerSkill":
                return eff_without_cond(eff, rep, st, eqp_flag, basic_flag) * get_per_skill_cnt_pos(pos, eff["conditionValue"])
            return 0

        # Compute per-dish max_limit, reduced material costs, and unit_price(cnt)
        dish_entries = []
        for p in range(n):
            st = states[p]
            ch = st["chef"]
            for s_idx, rep in enumerate(reps_by_pos[p]):
                grade = grades_by_pos[p][s_idx]
                rty = rep["rarity"]
                # Max limit
                lim_origin = rep["limit"] + self.ulti[f"MaxLimit_{rty}"]
                if disable_multi:
                    max_lim = 1
                else:
                    lim_buff = 0
                    for e in st["amber_effect"]:
                        if e.get("type") == "MaxEquipLimit" and e.get("rarity") == rty:
                            lim_buff += e["value"]
                    for e in st["sum_skill_effect"]:
                        if e.get("type") == "MaxEquipLimit" and e.get("rarity") == rty and e.get("condition") == "Self":
                            lim_buff += e["value"]
                    for e in st["partial_limit_effs"]:
                        if e.get("rarity") == rty and (set(e.get("conditionValueList", [])) & ch["tags"]):
                            lim_buff += e["value"]
                    max_lim = lim_origin + lim_buff

                # Material cost per portion
                mat_cost = {}
                for m in rep.get("materials", []):
                    mid = m["material"]
                    q = m["quantity"]
                    for mset, red in st["material_reduce"]:
                        if mid in mset:
                            q = max(1, q - red)
                    mat_cost[mid] = mat_cost.get(mid, 0) + q

                # Compute unit price function of rep_cnt
                def calc_unit_price(rep_cnt, p=p, rep=rep, st=st, ch=ch, grade=grade):
                    if grade < 1:
                        return 0, 0
                    rty_l = rep["rarity"]
                    buff = 100 + self.ulti[f"PriceBuff_{rty_l}"]
                    buff_rule = 0
                    rid_str = str(rep["id"])
                    if rid_str in rec_eff_map:
                        buff_rule += rec_eff_map[rid_str] * 100
                    elif rep["id"] in rec_eff_map:
                        buff_rule += rec_eff_map[rep["id"]] * 100
                    buff += buff_rule
                    for tag in ch["tags"]:
                        tb = (chef_tag_eff.get(str(tag), chef_tag_eff.get(tag, 0)) or 0) * 100
                        buff += tb
                    buff += GRADE_BUFF.get(grade, 0)

                    basic_pct = 0
                    basic_abs = 0
                    buff_skill = 0
                    buff_equip = 0

                    for e in st["amber_effect"]:
                        buff_skill += eval_effect(e, rep, st, rep_cnt, grade, p, 0, 0)
                        if e.get("type") == "BasicPrice":
                            v = 0
                            if not e.get("conditionType"):
                                v = e["value"]
                            elif e.get("conditionType") == "PerRank":
                                v = e["value"] * get_per_rank_cnt(p, e["conditionValue"])
                            if e.get("cal") == "Percent":
                                basic_pct += v
                            else:
                                basic_abs += v

                    if not rule.get("DisableChefSkillEffect"):
                        for e in st["sum_skill_effect"]:
                            if e.get("condition") == "Partial":
                                continue
                            et = e.get("type", "")
                            if et == "BasicPrice":
                                v = 0
                                if not e.get("conditionType"):
                                    v = e["value"]
                                elif e.get("conditionType") == "PerRank":
                                    v = e["value"] * get_per_rank_cnt(p, e["conditionValue"])
                                else:
                                    v = eval_effect(e, rep, st, rep_cnt, grade, p, 0, 1)
                                if e.get("cal") == "Percent":
                                    basic_pct += v
                                else:
                                    basic_abs += v
                            elif et.startswith("BasicPrice") and e.get("condition") == "Self":
                                en = dict(e)
                                en["type"] = et[10:]
                                v = eval_effect(en, rep, st, rep_cnt, grade, p, 0, 0)
                                if e.get("cal") == "Percent":
                                    basic_pct += v
                                else:
                                    basic_abs += v
                            else:
                                buff_skill += eval_effect(e, rep, st, rep_cnt, grade, p, 0, 0)

                    if not rule.get("DisableEquipSkillEffect"):
                        for e in st["equip_effect"]:
                            et = e.get("type", "")
                            if et == "BasicPrice":
                                v = 0
                                if not e.get("conditionType"):
                                    v = e["value"]
                                elif e.get("conditionType") == "PerRank":
                                    v = e["value"] * get_per_rank_cnt(p, e["conditionValue"])
                                else:
                                    v = eval_effect(e, rep, st, rep_cnt, grade, p, 1, 1)
                                if e.get("cal") == "Percent":
                                    basic_pct += v
                                else:
                                    basic_abs += v
                            elif et.startswith("BasicPrice"):
                                en = dict(e)
                                en["type"] = et[10:]
                                v = eval_effect(en, rep, st, rep_cnt, grade, p, 1, 0)
                                if e.get("cal") == "Percent":
                                    basic_pct += v
                                else:
                                    basic_abs += v
                            else:
                                buff_equip += eval_effect(e, rep, st, rep_cnt, grade, p, 1, 0)

                    for e in on_site_effects:
                        et = e.get("type", "")
                        if et == "BasicPrice":
                            v = eval_effect(e, rep, st, rep_cnt, grade, p, 0, 1)
                            if e.get("cal") == "Percent":
                                basic_pct += v
                            else:
                                basic_abs += v
                        elif et.startswith("BasicPrice"):
                            en = dict(e)
                            en["type"] = et[10:]
                            v = eval_effect(en, rep, st, rep_cnt, grade, p, 0, 0)
                            if e.get("cal") == "Percent":
                                basic_pct += v
                            else:
                                basic_abs += v
                        else:
                            buff_skill += eval_effect(e, rep, st, rep_cnt, grade, p, 0, 0)

                    total_buff = buff + buff_equip + buff_skill
                    ex_add = rep["exPrice"] if (use_real_ex and rep["ex"]) else 0
                    base_p = math.floor((rep["price"] + ex_add + basic_abs) * (100 + basic_pct) / 100.0)
                    unit_p = math.ceil(base_p * total_buff / 100.0)
                    return unit_p, total_buff

                # Evaluate at max_lim as representative unit price (almost always constant wrt cnt)
                u_price, u_buff = calc_unit_price(max_lim)
                dish_entries.append({
                    "pos": p,
                    "slot": s_idx,
                    "rep": rep,
                    "grade": grade,
                    "max_lim": max_lim if grade >= 1 else 0,
                    "mat_cost": mat_cost,
                    "unit_price": u_price,
                    "buff": u_buff,
                    "calc_fn": calc_unit_price,
                })

        # Allocate counts respecting MaterialsLimit
        if counts is not None:
            used_counts = list(counts)
        elif not mat_limit_raw:
            used_counts = [d["max_lim"] for d in dish_entries]
        else:
            if isinstance(mat_limit_raw, dict):
                remain = {int(k): int(v) for k, v in mat_limit_raw.items()}
            else:
                remain = {m["materialId"]: int(mat_limit_raw) for m in self.gd["materials"]}

            # First check if everything fits at max_lim
            needed = defaultdict(int)
            for d in dish_entries:
                for mid, q in d["mat_cost"].items():
                    needed[mid] += q * d["max_lim"]

            if all(needed[mid] <= remain.get(mid, 0) for mid in needed):
                used_counts = [d["max_lim"] for d in dish_entries]
            else:
                # Optimize counts via greedy by score per bottleneck resource + local swaps
                used_counts = [0] * len(dish_entries)
                # Compute bottleneck score: rank dishes by unit_price / sum(q / remain[m])
                order = sorted(
                    range(len(dish_entries)),
                    key=lambda idx: (
                        dish_entries[idx]["unit_price"]
                        / max(1e-9, sum(q / max(1, remain.get(mid, 1)) for mid, q in dish_entries[idx]["mat_cost"].items() if needed[mid] > remain.get(mid, 0)))
                        if any(needed[mid] > remain.get(mid, 0) for mid in dish_entries[idx]["mat_cost"])
                        else 1e12 + dish_entries[idx]["unit_price"]
                    ),
                    reverse=True,
                )
                rem = dict(remain)
                for idx in order:
                    d = dish_entries[idx]
                    if d["max_lim"] <= 0 or d["unit_price"] <= 0:
                        continue
                    cap = d["max_lim"]
                    for mid, q in d["mat_cost"].items():
                        cap = min(cap, rem.get(mid, 0) // q)
                    used_counts[idx] = cap
                    for mid, q in d["mat_cost"].items():
                        rem[mid] = rem.get(mid, 0) - q * cap

                # Quick pairwise refinement: try transferring 1..k portions from lower-efficiency to higher-efficiency
                improved = True
                while improved:
                    improved = False
                    for i in range(len(dish_entries)):
                        di = dish_entries[i]
                        if used_counts[i] >= di["max_lim"] or di["unit_price"] <= 0:
                            continue
                        # Find blocking materials for +1 of dish i
                        blockers = [mid for mid, q in di["mat_cost"].items() if rem.get(mid, 0) < q]
                        if not blockers:
                            used_counts[i] += 1
                            for mid, q in di["mat_cost"].items():
                                rem[mid] -= q
                            improved = True
                            continue
                        # Try reducing 1 dish j that frees all blockers
                        best_j = -1
                        best_gain = 0
                        for j in range(len(dish_entries)):
                            if j == i or used_counts[j] <= 0:
                                continue
                            dj = dish_entries[j]
                            if all(dj["mat_cost"].get(mid, 0) > 0 for mid in blockers):
                                # How many units of j needed to free blockers?
                                need_j = max(math.ceil((di["mat_cost"][mid] - rem.get(mid, 0)) / dj["mat_cost"][mid]) for mid in blockers)
                                if need_j <= used_counts[j]:
                                    gain = di["unit_price"] - need_j * dj["unit_price"]
                                    if gain > best_gain:
                                        best_gain = gain
                                        best_j = (j, need_j)
                        if best_j != -1:
                            j, need_j = best_j
                            dj = dish_entries[j]
                            used_counts[j] -= need_j
                            for mid, q in dj["mat_cost"].items():
                                rem[mid] += q * need_j
                            used_counts[i] += 1
                            for mid, q in di["mat_cost"].items():
                                rem[mid] -= q
                            improved = True

        # Final exact sum (re-evaluating unit price with actual count for ExcessCookbookNum/FewerCookbookNum)
        total = 0
        details = []
        for idx, d in enumerate(dish_entries):
            c = used_counts[idx]
            up, ub = d["calc_fn"](c) if c > 0 else (0, 0)
            sc = up * c
            total += sc
            details.append({
                "pos": d["pos"],
                "chef": states[d["pos"]]["chef"]["name"],
                "chef_id": states[d["pos"]]["chef"]["id"],
                "equip": states[d["pos"]]["equip"]["name"] if states[d["pos"]]["equip"] else "无",
                "equip_id": states[d["pos"]]["equip"]["equipId"] if states[d["pos"]]["equip"] else 0,
                "recipe": d["rep"]["name"],
                "recipe_id": d["rep"]["id"],
                "rarity": d["rep"]["rarity"],
                "ex": d["rep"]["ex"],
                "grade": GRADE_CN.get(d["grade"], "?"),
                "cnt": c,
                "max_lim": d["max_lim"],
                "unit_price": up,
                "buff": ub,
                "score": sc,
                "rule_mult": (rec_eff_map.get(str(d["rep"]["id"]), rec_eff_map.get(d["rep"]["id"], 0))),
            })

        return total, details


def solve_rule(ctx: GameContext, rule: dict, swap_equips=False, restarts=16, iters=2500, seed=42):
    rng = random.Random(seed)
    rec_eff_map = rule.get("RecipeEffect") or {}
    disable_multi = bool(rule.get("DisableMultiCookbook"))
    rarity_lim = rule.get("CookbookRarityLimit") or 6

    # 1. Filter and rank candidate owned recipes
    cand_recipes = []
    for r in ctx.owned_recipes:
        if r["rarity"] > rarity_lim:
            continue
        rm = rec_eff_map.get(str(r["id"]), rec_eff_map.get(r["id"], 0))
        eff_buff = 100 + ctx.ulti[f"PriceBuff_{r['rarity']}"] + rm * 100 + 100  # assume 神/传
        if eff_buff <= 0:
            continue
        base_p = r["price"] + (r["exPrice"] if r["ex"] else 0)
        lim = 1 if disable_multi else (r["limit"] + ctx.ulti[f"MaxLimit_{r['rarity']}"])
        est = base_p * eff_buff * lim / 100.0
        cand_recipes.append((est, r))
    cand_recipes.sort(key=lambda x: x[0], reverse=True)
    top_recipes = [r for _, r in cand_recipes[:100]]
    top_recipe_ids = [r["id"] for r in top_recipes]

    # 2. Pre-score owned chefs on top 40 recipes (solo score + aura detection)
    top40_ids = top_recipe_ids[:40]
    chef_scores = []
    aura_chef_ids = set()
    for ch in ctx.owned_chefs:
        # Check if chef has strong Partial/Next price or limit aura
        has_aura = False
        for e in ch["skill_effect"]:
            if e.get("condition") in ("Partial", "Next") and judge_eff(e):
                has_aura = True
        for uid, sk in ch["ultimate_list"]:
            if uid in ctx.ult_unlocked_uids:
                for e in sk.get("effect", []):
                    if e.get("condition") in ("Partial", "Next") and judge_eff(e):
                        has_aura = True
        if has_aura:
            aura_chef_ids.add(ch["id"])

        # Estimate solo top-3 recipe score
        st = ctx.build_lineup_state([ch["id"]], [ch["default_equip"]], rule)[0]
        sk_last = st["skills_last"]
        best3 = []
        for r in top_recipes[:45]:
            g = ctx.get_grade(sk_last, r, rule)
            if g < 1:
                continue
            rm = rec_eff_map.get(str(r["id"]), rec_eff_map.get(r["id"], 0))
            buff = 100 + ctx.ulti[f"PriceBuff_{r['rarity']}"] + rm * 100 + GRADE_BUFF[g]
            base_p = r["price"] + (r["exPrice"] if r["ex"] else 0)
            lim = 1 if disable_multi else (r["limit"] + ctx.ulti[f"MaxLimit_{r['rarity']}"])
            best3.append(base_p * buff * lim / 100.0)
        best3.sort(reverse=True)
        solo_est = sum(best3[:3])
        chef_scores.append((solo_est, ch["id"]))

    chef_scores.sort(key=lambda x: x[0], reverse=True)
    cand_chef_ids = [cid for _, cid in chef_scores[:90]]
    for aid in aura_chef_ids:
        if aid not in cand_chef_ids:
            cand_chef_ids.append(aid)

    # Candidate equips pool (if swap_equips=True): top equips with price/skill/limit buffs
    cand_equip_ids = [0]
    if swap_equips:
        for eid in ctx.known_equip_ids:
            eq = ctx.equips_by_id.get(eid)
            if not eq:
                continue
            if any(judge_eff(e) or e.get("type") in SKILL_KEYS_CAP for e in eq["effect"]):
                cand_equip_ids.append(eid)

    def default_equips_for(cids):
        return [ctx.chefs_by_id[c]["default_equip"] for c in cids]

    def greedy_assign_recipes(cids, eids, pool_ids):
        """Greedily pick 9 distinct recipes for the 3 chefs given current lineup."""
        states = ctx.build_lineup_state(cids, eids, rule)
        used = set()
        groups = [[], [], []]
        # Score each (pos, rid) pair quickly
        pairs = []
        for p in range(3):
            sk_last = states[p]["skills_last"]
            for rid in pool_ids:
                r = ctx.recipes_by_id[rid]
                g = ctx.get_grade(sk_last, r, rule)
                if g < 1:
                    continue
                rm = rec_eff_map.get(str(rid), rec_eff_map.get(rid, 0))
                buff = 100 + ctx.ulti[f"PriceBuff_{r['rarity']}"] + rm * 100 + GRADE_BUFF[g]
                base_p = r["price"] + (r["exPrice"] if r["ex"] else 0)
                lim = 1 if disable_multi else (r["limit"] + ctx.ulti[f"MaxLimit_{r['rarity']}"])
                pairs.append((base_p * buff * lim, p, rid))
        pairs.sort(reverse=True)
        for _, p, rid in pairs:
            if len(groups[p]) < 3 and rid not in used:
                groups[p].append(rid)
                used.add(rid)
            if all(len(g) == 3 for g in groups):
                break
        # Fill any missing slots
        for p in range(3):
            for rid in pool_ids:
                if len(groups[p]) >= 3:
                    break
                if rid not in used:
                    groups[p].append(rid)
                    used.add(rid)
        return groups

    best_score = -1
    best_state = None
    best_details = None

    top_chef_pool = cand_chef_ids[:40]

    for rs in range(restarts):
        if rs == 0:
            cids = list(cand_chef_ids[:3])
        else:
            cids = rng.sample(top_chef_pool if rs < restarts // 2 else cand_chef_ids, 3)
        eids = default_equips_for(cids) if not swap_equips else [
            ctx.chefs_by_id[c]["default_equip"] for c in cids
        ]
        # Ensure unique equips if swap_equips
        if swap_equips:
            seen_e = set()
            for i in range(3):
                if eids[i] and eids[i] in seen_e:
                    eids[i] = 0
                if eids[i]:
                    seen_e.add(eids[i])

        groups = greedy_assign_recipes(cids, eids, top_recipe_ids[:60])
        cur_score, cur_details = ctx.evaluate_lineup(cids, eids, groups, rule)
        if cur_score > best_score:
            best_score, best_state, best_details = cur_score, (list(cids), list(eids), [list(g) for g in groups]), cur_details

        t0 = max(cur_score * 0.08, 500.0)
        t1 = max(cur_score * 0.0005, 5.0)

        for step in range(iters):
            temp = t0 * ((t1 / t0) ** (step / iters))
            ncids = list(cids)
            neids = list(eids)
            ngroups = [list(g) for g in groups]

            move = rng.random()
            if move < 0.25:
                # Replace one chef
                pos = rng.randrange(3)
                pool = cand_chef_ids
                new_c = rng.choice(pool)
                if new_c in ncids:
                    continue
                ncids[pos] = new_c
                if not swap_equips:
                    neids[pos] = ctx.chefs_by_id[new_c]["default_equip"]
            elif move < 0.35:
                # Swap two chefs (order matters for Next skills & dish assignment)
                i, j = rng.sample(range(3), 2)
                ncids[i], ncids[j] = ncids[j], ncids[i]
                neids[i], neids[j] = neids[j], neids[i]
                if rng.random() < 0.5:
                    ngroups[i], ngroups[j] = ngroups[j], ngroups[i]
            elif move < 0.78:
                # Replace one recipe with another unused recipe from top_recipe_ids
                pos = rng.randrange(3)
                slot = rng.randrange(len(ngroups[pos]))
                used_r = {r for g in ngroups for r in g}
                new_r = rng.choice(top_recipe_ids)
                if new_r in used_r:
                    continue
                ngroups[pos][slot] = new_r
            elif move < 0.90:
                # Swap two recipes between two chefs
                p1, p2 = rng.sample(range(3), 2)
                s1 = rng.randrange(len(ngroups[p1]))
                s2 = rng.randrange(len(ngroups[p2]))
                ngroups[p1][s1], ngroups[p2][s2] = ngroups[p2][s2], ngroups[p1][s1]
            else:
                if swap_equips and len(cand_equip_ids) > 3:
                    pos = rng.randrange(3)
                    new_e = rng.choice(cand_equip_ids)
                    if new_e != 0 and new_e in neids:
                        continue
                    neids[pos] = new_e
                else:
                    # Re-greedy recipes for current chefs
                    ngroups = greedy_assign_recipes(ncids, neids, top_recipe_ids[:70])

            nscore, ndetails = ctx.evaluate_lineup(ncids, neids, ngroups, rule)
            diff = nscore - cur_score
            if diff >= 0 or rng.random() < math.exp(diff / max(temp, 1e-6)):
                cids, eids, groups = ncids, neids, ngroups
                cur_score, cur_details = nscore, ndetails
                if cur_score > best_score:
                    best_score = cur_score
                    best_state = (list(cids), list(eids), [list(g) for g in groups])
                    best_details = ndetails

    # Final deterministic polish on best_state (check all recipes in top 100 for each of the 9 slots)
    cids, eids, groups = best_state
    polished = True
    while polished:
        polished = False
        used_r = {r for g in groups for r in g}
        for p in range(3):
            for s in range(len(groups[p])):
                orig = groups[p][s]
                best_r = orig
                for cand_r in top_recipe_ids:
                    if cand_r in used_r:
                        continue
                    groups[p][s] = cand_r
                    sc, det = ctx.evaluate_lineup(cids, eids, groups, rule)
                    if sc > best_score:
                        best_score, best_details = sc, det
                        best_r = cand_r
                        polished = True
                used_r.discard(orig)
                groups[p][s] = best_r
                used_r.add(best_r)

    return best_score, (cids, eids, groups), best_details


def print_result(rule, score, details):
    pass_line = rule.get("PassLine") or []
    tier_str = ""
    if len(pass_line) == 3:
        if score >= pass_line[0]:
            tier_str = f"【稳过高保 {pass_line[0]}！】"
        elif score >= pass_line[1]:
            tier_str = f"【过中保 {pass_line[1]}，距高保差 {pass_line[0] - score}】"
        elif score >= pass_line[2]:
            tier_str = f"【过低保 {pass_line[2]}】"
        else:
            tier_str = f"【未达低保 {pass_line[2]}】"
    elif len(pass_line) == 1:
        tier_str = f"【{'过线！' if score >= pass_line[0] else '未过线'} 目标 {pass_line[0]}】"

    print(f"\n==================== {rule['Title']} ====================")
    print(f"规则说明: {rule.get('message', '')}")
    print(f"预计总分: {score:,}  {tier_str}")
    by_pos = defaultdict(list)
    for d in details:
        by_pos[d["pos"]].append(d)
    for p in range(3):
        items = by_pos[p]
        if not items:
            continue
        c_name = items[0]["chef"]
        eq_name = items[0]["equip"]
        sub_tot = sum(x["score"] for x in items)
        print(f"  [位置 {p+1}] 厨师: {c_name} | 厨具: {eq_name} | 小计: {sub_tot:,}")
        for x in items:
            ex_tag = "专精" if x["ex"] else "未专"
            rm_tag = f"规则{x['rule_mult']:+.0f}倍" if x["rule_mult"] else "无倍"
            print(
                f"      - {x['recipe']} ({x['rarity']}火/{ex_tag}/{x['grade']}) "
                f"x {x['cnt']}份 (上限{x['max_lim']}) | 单价 {x['unit_price']} ({rm_tag}, 总加成{x['buff']:.0f}%) => {x['score']:,}"
            )


def main():
    parser = argparse.ArgumentParser(description="爆炒江湖自动配队求解器")
    parser.add_argument("--token", required=True, help="白菜菊花校验码")
    parser.add_argument("--rules", default="1,7,8,9", help="逗号分隔的规则 ID (foodgod_rule.json)")
    parser.add_argument("--swap-equips", action="store_true", help="允许从已有已装备厨具池中调换厨具")
    parser.add_argument("--refresh", action="store_true", help="强制重新拉取线上数据")
    parser.add_argument("--restarts", type=int, default=14)
    parser.add_argument("--iters", type=int, default=2200)
    args = parser.parse_args()

    gd = load_or_fetch(os.path.join(DATA_DIR, "data.min.json"), DATA_URL, refresh=args.refresh)
    fg = load_or_fetch(os.path.join(DATA_DIR, "foodgod_rule.json"), RULE_URL, refresh=args.refresh)
    user_path = os.path.join(DATA_DIR, f"user_{args.token}.json")
    user_archive = load_or_fetch(user_path, ARCHIVE_URL.format(token=args.token), refresh=args.refresh)

    if user_archive.get("ret") != "S":
        print("拉取账号数据失败:", user_archive)
        sys.exit(1)

    ctx = GameContext(gd, user_archive)
    print(
        f"账号 [{args.token}] 加载完成: 厨师 {len(ctx.owned_chefs)} (已修炼 {sum(1 for c in ctx.owned_chefs if c['ult'])}), "
        f"菜谱 {len(ctx.owned_recipes)} (已专精 {sum(1 for r in ctx.owned_recipes if r['ex'])}), "
        f"全局技法加成: 炒+{ctx.ulti['Stirfry']} 煮+{ctx.ulti['Boil']} 切+{ctx.ulti['Knife']} "
        f"炸+{ctx.ulti['Fry']} 烤+{ctx.ulti['Bake']} 蒸+{ctx.ulti['Steam']} | "
        f"全+{ctx.ulti['All']} 男+{ctx.ulti['Male']} 女+{ctx.ulti['Female']}"
    )
    print(
        f"全局菜谱售价加成: "
        + " ".join(f"{i}火+{ctx.ulti[f'PriceBuff_{i}']}%" for i in range(1, 6))
        + " | 份数上限: "
        + " ".join(f"{i}火+{ctx.ulti[f'MaxLimit_{i}']}" for i in range(1, 6))
    )

    rules_by_id = {r["Id"]: r for r in fg.get("rules", [])}
    rule_ids = [int(x.strip()) for x in args.rules.split(",") if x.strip()]
    for rid in rule_ids:
        rule = rules_by_id.get(rid)
        if not rule:
            print(f"未找到规则 ID={rid}")
            continue
        score, state, details = solve_rule(
            ctx, rule, swap_equips=args.swap_equips, restarts=args.restarts, iters=args.iters
        )
        print_result(rule, score, details)


if __name__ == "__main__":
    main()
