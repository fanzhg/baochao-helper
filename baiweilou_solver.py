#!/usr/bin/env python3
"""
爆炒江湖《百味楼》专用自动配队求解器（已通过游戏实测 0 误差校准）

已验证的核心引擎规则（对齐 2026-11-27 实测 10,160 分，6维+5菜全部 0 误差）：
1. 每层食客固定点单 5 道菜（有无菜谱均可做；拥有且已专精按专精价计算，无装修加成）。
2. 合并总属性池：上阵厨师各自面板相加 + 全局修炼单技法/全技法加 1 次 + 阵容含男厨加 1 次男厨加成 + 含女厨加 1 次女厨加成。
3. 品级与「超传」加成：
   - 1~4倍：可(+0%) / 优(+10%) / 特(+30%) / 神(+50%)
   - 5倍起：传(+100%)，10倍起：传^^(+200%)，20倍起：传^^^ (+300%)，30倍起：满传(+400%)
4. 技能合并（关键机制！）：
   - Self / 厨具 / 遗玉 / 接收到的 Next（下位）技能生效 1 次；
   - Partial（全场光环）对场上每位符合条件的厨师各生效 1 次并汇入总池（即 N 人位无条件光环直接乘以 N！同理负面全场光环如吕布 -30% 也会乘以 N）。
5. 菜谱最终单价：ceil( floor((base + ex + basicAbs) * (100 + basicPct) / 100) * (100 + globalPriceBuff + gradeBuff + skillBuff) / 100 )
"""

import argparse
import json
import math
import os
import random
from collections import defaultdict

from bcjh_solver import (
    DATA_DIR,
    DATA_URL,
    ARCHIVE_URL,
    SKILL_KEYS_CAP,
    SKILL_KEYS_LOW,
    SKILL_CN,
    CONDIMENT_TYPES,
    MATERIAL_TYPES,
    PER_SKILL_ORDER,
    GameContext,
    load_or_fetch,
    judge_eff,
)


def baiweilou_grade(pool_skills, rep):
    """
    Return (grade_level, grade_label, grade_buff_pct, min_ratio).
    Calibrated from live Floor 1 (10,160) & Floor 2 (13,528) observations (0 error on both):
      4.96x  -> 神   (+50%)
      10.03x, 10.21x -> 传^  (+150%)
      11.85x, 12.49x, 14.32x, 15.26x -> 传^^ (+200%)
      24.43x -> 传^^^ (+300%)
      36.65x, 36.74x, 71.44x -> 满传 (+400%)
    """
    min_ratio = 9999.0
    for sk, req in rep["skills"].items():
        if req <= 0:
            continue
        r = pool_skills.get(sk, 0) / req
        if r < min_ratio:
            min_ratio = r
    if min_ratio < 1:
        return 0, "不足", 0, min_ratio
    elif min_ratio < 2:
        return 1, "可", 0, min_ratio
    elif min_ratio < 3:
        return 2, "优", 10, min_ratio
    elif min_ratio < 4:
        return 3, "特", 30, min_ratio
    elif min_ratio < 5:
        return 4, "神", 50, min_ratio
    elif min_ratio < 6:
        return 5, "传", 100, min_ratio
    elif min_ratio < 11:
        return 6, "传^", 150, min_ratio
    elif min_ratio < 16:
        return 7, "传^^", 200, min_ratio
    elif min_ratio < 21:
        return 8, "传^^+", 250, min_ratio
    elif min_ratio < 26:
        return 9, "传^^^", 300, min_ratio
    else:
        return 10, "满传", 400, min_ratio


class BaiweilouSolver:
    def __init__(self, ctx: GameContext):
        self.ctx = ctx
        self.recipes_by_name = {r["name"]: r for r in ctx.recipes_by_id.values()}
        self.dummy_rule = {"DisableDecorationEffect": 1}

    def resolve_dishes(self, dish_names):
        dishes = []
        for nm in dish_names:
            nm = nm.strip()
            if nm not in self.recipes_by_name:
                raise ValueError(f"未在图鉴中找到菜谱: {nm}")
            dishes.append(self.recipes_by_name[nm])
        return dishes

    def build_baiweilou_pool(self, chef_ids, equip_ids):
        """
        Compute exact Baiweilou merged 6-stat pool and per-chef skill/equip/amber states.
        Global ulti skills are added ONCE for the pool (0 error vs live game).
        """
        n = len(chef_ids)
        chefs = [self.ctx.chefs_by_id[cid] for cid in chef_ids]
        equips = [self.ctx.equips_by_id.get(eid) if eid else None for eid in equip_ids]

        ambers_list = []
        for ch in chefs:
            ambs = []
            disk = self.ctx.disks_by_id.get(ch.get("disk"))
            slot_types = list(disk["info"]) + [0] if disk else [0]
            for idx, aid in enumerate(ch.get("default_ambers") or []):
                if idx >= len(slot_types) or not aid:
                    continue
                amb = self.ctx.ambers_by_id.get(aid)
                if amb:
                    st = slot_types[idx]
                    if st == 0 or amb.get("type") == 4 or amb.get("type") == st:
                        ambs.append(amb)
            ambers_list.append(ambs)

        disk_sources = [self.ctx.get_chef_disk_sources(chefs[i], equips[i], ambers_list[i], self.dummy_rule) for i in range(n)]

        pool_skills = {kl: 0 for kl in SKILL_KEYS_LOW}
        chef_states = []

        for pos in range(n):
            ch = chefs[pos]
            eqp = equips[pos]
            ambs = ambers_list[pos]
            last_ch = chefs[pos - 1] if pos > 0 else None

            base_dlv = ch.get("default_dlv", 1)
            dlv_bonus = self.ctx.disk_level_bonus(disk_sources[pos], {"Self"})
            prev_idx = pos - 1 if pos > 0 else None
            for k in range(n):
                conds = {"Partial", "Next"} if k == prev_idx else {"Partial"}
                dlv_bonus += self.ctx.disk_level_bonus(disk_sources[k], conds)
            eff_dlv = base_dlv + dlv_bonus

            muti_eq = 0
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ctx.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if e.get("type") == "MutiEquipmentSkill" and e.get("cal") == "Percent":
                            muti_eq += e.get("value", 0)

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

            suit_effs = [e for e in self.ctx.get_amber_suit_effects(ambs) if judge_eff(e)]

            # Individual 6-stat calculation (WITHOUT global ulti — global ulti is added once to pool)
            ind_skills = {}
            for kc, kl in zip(SKILL_KEYS_CAP, SKILL_KEYS_LOW):
                base_v = ch["skills"][kl]
                add_v = 0
                pct_v = 0
                for e in ch["skill_effect"]:
                    if e.get("type") == kc:
                        if e.get("cal") == "Abs":
                            add_v += e["value"]
                        elif e.get("cal") == "Percent":
                            pct_v += e["value"]
                for tag in ch["tags"]:
                    if tag in self.ctx.qixia_skill_by_tag:
                        add_v += self.ctx.qixia_skill_by_tag[tag][kc]
                for uid, sk in ch["ultimate_list"]:
                    if uid in self.ctx.ult_unlocked_uids:
                        for e in sk.get("effect", []):
                            if e.get("type") == kc and e.get("condition") == "Self":
                                if e.get("cal") == "Abs":
                                    add_v += e["value"]
                                elif e.get("cal") == "Percent":
                                    pct_v += e["value"]
                # Partial stat auras from all onsite chefs
                for k in range(n):
                    cur_ch = chefs[k]
                    for uid, sk in cur_ch["ultimate_list"]:
                        if uid in self.ctx.ult_unlocked_uids:
                            for e in sk.get("effect", []):
                                if e.get("type") == kc and e.get("condition") == "Partial":
                                    if e.get("conditionType") == "ChefTag":
                                        ok = bool(set(e.get("conditionValueList", [])) & ch["tags"])
                                    else:
                                        ok = True
                                    if ok:
                                        if e.get("cal") == "Abs":
                                            add_v += e["value"]
                                        elif e.get("cal") == "Percent":
                                            pct_v += e["value"]
                if last_ch:
                    for uid, sk in last_ch["ultimate_list"]:
                        if uid in self.ctx.ult_unlocked_uids:
                            for e in sk.get("effect", []):
                                if e.get("type") == kc and e.get("condition") == "Next":
                                    if e.get("cal") == "Abs":
                                        add_v += e["value"]
                                    elif e.get("cal") == "Percent":
                                        pct_v += e["value"]
                if eqp:
                    for e in eqp["effect"]:
                        if e.get("type") == kc:
                            if e.get("cal") == "Abs":
                                add_v += e["value"] * (100 + muti_eq) / 100.0
                            elif e.get("cal") == "Percent":
                                pct_v += e["value"] * (100 + muti_eq) / 100.0
                for e in ambers_all_eff:
                    if e.get("type") == kc:
                        if e.get("cal") == "Abs":
                            add_v += e["value"]
                        elif e.get("cal") == "Percent":
                            pct_v += e["value"]
                final_v = base_v + add_v + math.ceil((base_v + add_v) * pct_v / 100.0)
                ind_skills[kl] = final_v
                pool_skills[kl] += final_v

            # Collect this chef's Self / Next / Partial price effects
            self_effs = []
            partial_effs = []
            for e in ch["skill_effect"]:
                if not judge_eff(e):
                    continue
                if e.get("condition") == "Partial":
                    partial_effs.append(e)
                elif e.get("condition") != "Next":
                    self_effs.append(e)
            if last_ch:
                for e in last_ch["skill_effect"]:
                    if e.get("condition") == "Next" and judge_eff(e):
                        self_effs.append(e)
                for uid, sk in last_ch["ultimate_list"]:
                    if uid in self.ctx.ult_unlocked_uids:
                        for e in sk.get("effect", []):
                            if e.get("condition") == "Next" and judge_eff(e):
                                self_effs.append(e)
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ctx.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if not judge_eff(e) or e.get("condition") == "Next":
                            continue
                        if e.get("condition") == "Partial":
                            partial_effs.append(e)
                        else:
                            self_effs.append(e)
            self_effs.extend(suit_effs)
            equip_effs = [e for e in (eqp["effect"] if eqp else []) if judge_eff(e)]

            chef_states.append({
                "chef": ch,
                "equip": eqp,
                "ambers": ambs,
                "ind_skills": ind_skills,
                "self_effs": self_effs,
                "partial_effs": partial_effs,
                "equip_effs": equip_effs,
                "amber_effs": amber_price_eff,
                "muti_eq": muti_eq,
            })

        # Add global ulti skills ONCE to the merged pool
        has_male = any(1 in ch["tags"] for ch in chefs)
        has_female = any(2 in ch["tags"] for ch in chefs)
        for kc, kl in zip(SKILL_KEYS_CAP, SKILL_KEYS_LOW):
            pool_skills[kl] += self.ctx.ulti[kc] + self.ctx.ulti["All"]
            if has_male:
                pool_skills[kl] += self.ctx.ulti["Male"]
            if has_female:
                pool_skills[kl] += self.ctx.ulti["Female"]

        return pool_skills, chef_states

    def evaluate_team(self, chef_ids, dishes, equip_ids=None):
        if equip_ids is None:
            equip_ids = [self.ctx.chefs_by_id[c]["default_equip"] for c in chef_ids]

        pool_skills, chef_states = self.build_baiweilou_pool(chef_ids, equip_ids)
        n = len(chef_states)

        # Grades for all 5 dishes
        grade_infos = [baiweilou_grade(pool_skills, d) for d in dishes]

        def per_rank_cnt(cond_val):
            # Map cond_val (1..5) against grade_level (any super-legend >= 5 satisfies Rank 5)
            return sum(1 for gl, _, _, _ in grade_infos if gl >= cond_val)

        def per_skill_cnt(cond_val):
            sk = PER_SKILL_ORDER[cond_val - 1]
            return sum(1 for d in dishes if sk in d["skills"])

        # Expand all effects into (eff, weight, muti_eq, is_equip)
        # KEY CALIBRATED RULE:
        #   - Self / Next / Equip / Amber apply 1x
        #   - Partial applies once PER matching deployed chef (so unconditional Partial applies N times!)
        merged_effects = []
        for st in chef_states:
            muti_eq = st["muti_eq"]
            for e in st["self_effs"]:
                merged_effects.append((e, 1, 0, False))
            for e in st["amber_effs"]:
                merged_effects.append((e, 1, 0, False))
            for e in st["equip_effs"]:
                merged_effects.append((e, 1, muti_eq, True))
            for e in st["partial_effs"]:
                if e.get("conditionType") == "ChefTag":
                    cvl = set(e.get("conditionValueList", []))
                    cnt = sum(1 for other in chef_states if cvl & other["chef"]["tags"])
                    if cnt > 0:
                        ec = dict(e)
                        ec.pop("conditionType", None)
                        merged_effects.append((ec, cnt, 0, False))
                else:
                    merged_effects.append((e, n, 0, False))

        def eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag=0):
            et = eff.get("type", "")
            muti = (100 + muti_eq) / 100.0 if is_equip else 1.0
            val = eff.get("value", 0) * muti
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

        def eval_one(eff, rep, gl, muti_eq, is_equip, basic_flag=0):
            ct = eff.get("conditionType")
            if not ct:
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag)
            elif ct == "Rank":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if gl >= eff["conditionValue"] else 0
            elif ct == "PerRank":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) * per_rank_cnt(eff["conditionValue"])
            elif ct == "CookbookRarity":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if rep["rarity"] in eff.get("conditionValueList", []) else 0
            elif ct == "CookbookTag":
                mc = len(set(eff.get("conditionValueList", [])) & rep["tags"])
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) * mc if mc > 0 else 0
            elif ct == "CookbookTagOnce":
                mc = len(set(eff.get("conditionValueList", [])) & rep["tags"])
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if mc > 0 else 0
            elif ct == "PerSkill":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) * per_skill_cnt(eff["conditionValue"])
            elif ct == "FewerCookbookNum":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if 1 <= eff["conditionValue"] else 0
            elif ct == "ExcessCookbookNum":
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if 1 >= eff["conditionValue"] else 0
            elif ct == "ChefTag":
                cvl = set(eff.get("conditionValueList", []))
                return eff_val_for_dish(eff, rep, muti_eq, is_equip, basic_flag) if any(cvl & s["chef"]["tags"] for s in chef_states) else 0
            return 0

        total_score = 0
        dish_details = []
        for idx, rep in enumerate(dishes):
            gl, glabel, gbuff, min_r = grade_infos[idx]
            base_ex = rep["price"] + (rep["exPrice"] if (rep["got"] and rep["ex"]) else 0)
            if gl < 1:
                dish_details.append({
                    "recipe": rep["name"], "rarity": rep["rarity"], "grade": "不足",
                    "ratio": min_r, "base": base_ex, "basic_pct": 0, "basic_abs": 0,
                    "total_buff": 0, "score": 0,
                })
                continue

            basic_pct = 0.0
            basic_abs = 0.0
            skill_buff = 0.0
            for eff, weight, muti_eq, is_equip in merged_effects:
                et = eff.get("type", "")
                if et == "BasicPrice":
                    ct = eff.get("conditionType")
                    if not ct:
                        v = eff["value"] * ((100 + muti_eq) / 100.0 if is_equip else 1.0)
                    elif ct == "PerRank":
                        v = eff["value"] * ((100 + muti_eq) / 100.0 if is_equip else 1.0) * per_rank_cnt(eff["conditionValue"])
                    else:
                        v = eval_one(eff, rep, gl, muti_eq, is_equip, basic_flag=1)
                    if eff.get("cal") == "Percent":
                        basic_pct += v * weight
                    else:
                        basic_abs += v * weight
                elif et.startswith("BasicPrice"):
                    en = dict(eff)
                    en["type"] = et[10:]
                    v = eval_one(en, rep, gl, muti_eq, is_equip, basic_flag=0)
                    if eff.get("cal") == "Percent":
                        basic_pct += v * weight
                    else:
                        basic_abs += v * weight
                else:
                    skill_buff += eval_one(eff, rep, gl, muti_eq, is_equip, basic_flag=0) * weight

            g_pb = self.ctx.ulti[f"PriceBuff_{rep['rarity']}"]
            total_buff = 100 + g_pb + gbuff + skill_buff
            adj_base = math.floor((base_ex + basic_abs) * (100 + basic_pct) / 100.0)
            sc = max(0, math.ceil(adj_base * total_buff / 100.0))
            total_score += sc
            dish_details.append({
                "recipe": rep["name"],
                "rarity": rep["rarity"],
                "grade": glabel,
                "ratio": min_r,
                "base": base_ex,
                "basic_pct": basic_pct,
                "basic_abs": basic_abs,
                "total_buff": total_buff,
                "score": sc,
            })

        return total_score, pool_skills, dish_details, chef_states

    def rank_chefs_for_dishes(self, dishes, slots=3, exclude_ids=None, max_rarity=5):
        exclude_ids = set(exclude_ids or [])
        ranked = []
        for ch in self.ctx.owned_chefs:
            cid = ch["id"]
            if cid in exclude_ids or ch["rarity"] > max_rarity:
                continue
            eqp = self.ctx.equips_by_id.get(ch["default_equip"])
            # Estimate marginal buff value accounting for Partial x slots scaling!
            val = 0.0
            eff_items = []
            for e in ch["skill_effect"]:
                if judge_eff(e):
                    eff_items.append((e, slots if e.get("condition") == "Partial" else 1))
            for uid, sk in ch["ultimate_list"]:
                if uid in self.ctx.ult_unlocked_uids:
                    for e in sk.get("effect", []):
                        if judge_eff(e):
                            eff_items.append((e, slots if e.get("condition") == "Partial" else 1))
            if eqp:
                for e in eqp["effect"]:
                    if judge_eff(e):
                        eff_items.append((e, 1))

            for d in dishes:
                bp = d["price"] + (d["exPrice"] if (d["got"] and d["ex"]) else 0)
                for e, w in eff_items:
                    et = e.get("type", "")
                    v = e.get("value", 0) * w
                    mult = 4.0 if et.startswith("BasicPrice") else 1.0
                    core = et[10:] if et.startswith("BasicPrice") else et
                    hit = False
                    if core == "CookbookPrice" or core == "":
                        hit = True
                    elif core.startswith("Use"):
                        sub = core[3:]
                        if (sub in SKILL_KEYS_CAP and sub.lower() in d["skills"]) or (
                            sub in MATERIAL_TYPES and sub.lower() in d["materials_type"]
                        ) or (sub in CONDIMENT_TYPES and d.get("condiment") == sub):
                            hit = True
                    if hit:
                        if e.get("conditionType") == "PerRank":
                            v *= 5
                        elif e.get("conditionType") == "PerSkill":
                            v *= 3
                        val += bp * v * mult / 100.0
            # Small tie-breaker for raw relevant skills (helps hit 传^^/传^^^/满传!)
            rel_skills = sum(ch["skills"].get(sk, 0) for d in dishes for sk in d["skills"])
            ranked.append((val + rel_skills * 0.25, rel_skills, cid))
        ranked.sort(reverse=True)
        return ranked

    def solve(self, dishes, slots=3, target=0, swap_equips=False, exclude_ids=None, max_rarity=5, seed=42):
        rng = random.Random(seed)
        ranked = self.rank_chefs_for_dishes(dishes, slots=slots, exclude_ids=exclude_ids, max_rarity=max_rarity)
        top_by_buff = [cid for _, _, cid in ranked[:85]]
        top_by_stat = [cid for _, _, cid in sorted(ranked, key=lambda x: x[1], reverse=True)[:35]]
        cand_ids = list(dict.fromkeys(top_by_buff + top_by_stat))

        cand_equips = [0]
        if swap_equips:
            eq_rank = []
            for eid in self.ctx.known_equip_ids:
                eq = self.ctx.equips_by_id.get(eid)
                if not eq:
                    continue
                score_e = 0.0
                for e in eq["effect"]:
                    et = e.get("type", "")
                    v = e.get("value", 0)
                    if et in SKILL_KEYS_CAP:
                        score_e += v * 5
                        continue
                    mult = 4.0 if et.startswith("BasicPrice") else 1.0
                    core = et[10:] if et.startswith("BasicPrice") else et
                    for d in dishes:
                        bp = d["price"] + (d["exPrice"] if (d["got"] and d["ex"]) else 0)
                        if core == "CookbookPrice" or core == "":
                            score_e += bp * v * mult
                        elif core.startswith("Use"):
                            sub = core[3:]
                            if (sub in SKILL_KEYS_CAP and sub.lower() in d["skills"]) or (
                                sub in MATERIAL_TYPES and sub.lower() in d["materials_type"]
                            ) or (sub in CONDIMENT_TYPES and d.get("condiment") == sub):
                                score_e += bp * v * mult
                if score_e > 0:
                    eq_rank.append((score_e, eid))
            eq_rank.sort(reverse=True)
            cand_equips = [0] + [eid for _, eid in eq_rank[:45]]

        best_sc = -1
        best_res = None

        for rs in range(14):
            if rs == 0:
                cids = list(cand_ids[:slots])
            else:
                pool = cand_ids[:40] if rs < 7 else cand_ids
                cids = rng.sample(pool, min(slots, len(pool)))
            eids = [self.ctx.chefs_by_id[c]["default_equip"] for c in cids]
            if swap_equips:
                eids = [cand_equips[min(i + 1, len(cand_equips) - 1)] for i in range(len(cids))]

            cur_sc, cur_pool, cur_det, cur_sts = self.evaluate_team(cids, dishes, eids)
            if cur_sc > best_sc:
                best_sc = cur_sc
                best_res = (list(cids), list(eids), cur_pool, cur_det, cur_sts)

            improved = True
            while improved:
                improved = False
                # 1. Try replacing each chef
                for p in range(len(cids)):
                    orig_c, orig_e = cids[p], eids[p]
                    for cand_c in cand_ids:
                        if cand_c in cids:
                            continue
                        cids[p] = cand_c
                        if not swap_equips:
                            eids[p] = self.ctx.chefs_by_id[cand_c]["default_equip"]
                        sc, pl, dt, sts = self.evaluate_team(cids, dishes, eids)
                        if sc > cur_sc:
                            cur_sc, cur_pool, cur_det, cur_sts = sc, pl, dt, sts
                            orig_c, orig_e = cand_c, eids[p]
                            improved = True
                            if cur_sc > best_sc:
                                best_sc = cur_sc
                                best_res = (list(cids), list(eids), pl, dt, sts)
                    cids[p], eids[p] = orig_c, orig_e

                # 2. Try swapping positions (matters for Next skills!)
                for i in range(len(cids)):
                    for j in range(i + 1, len(cids)):
                        cids[i], cids[j] = cids[j], cids[i]
                        eids[i], eids[j] = eids[j], eids[i]
                        sc, pl, dt, sts = self.evaluate_team(cids, dishes, eids)
                        if sc > cur_sc:
                            cur_sc, cur_pool, cur_det, cur_sts = sc, pl, dt, sts
                            improved = True
                            if cur_sc > best_sc:
                                best_sc = cur_sc
                                best_res = (list(cids), list(eids), pl, dt, sts)
                        else:
                            cids[i], cids[j] = cids[j], cids[i]
                            eids[i], eids[j] = eids[j], eids[i]

                # 3. Try swapping equips if enabled
                if swap_equips:
                    for p in range(len(cids)):
                        orig_e = eids[p]
                        for cand_e in cand_equips:
                            if cand_e != 0 and cand_e in eids:
                                continue
                            eids[p] = cand_e
                            sc, pl, dt, sts = self.evaluate_team(cids, dishes, eids)
                            if sc > cur_sc:
                                cur_sc, cur_pool, cur_det, cur_sts = sc, pl, dt, sts
                                orig_e = cand_e
                                improved = True
                                if cur_sc > best_sc:
                                    best_sc = cur_sc
                                    best_res = (list(cids), list(eids), pl, dt, sts)
                        eids[p] = orig_e

        return best_sc, best_res


def describe_chef_buffs(st):
    parts = []
    ch = st["chef"]
    if ch.get("skill_desc"):
        parts.append(ch["skill_desc"])
    for uid, sk in ch["ultimate_list"]:
        if sk.get("desc") and sk.get("skillCondition") in ("Self", "Partial", "Next"):
            parts.append("修炼:" + sk["desc"])
    if st["equip"] and st["equip"].get("skill_desc"):
        parts.append(f"厨具[{st['equip']['name']}]:" + st["equip"]["skill_desc"])
    return " | ".join(parts)


def print_baiweilou_result(title, score, target, res):
    cids, eids, pool, det, sts = res
    status = f"【稳过！超出目标 {score - target:+}】" if score >= target else f"【差 {target - score}】"
    print(f"\n==================== {title} ====================")
    print(f"预计总分: {score:,} / 目标 {target:,}  {status}")
    sk_str = " ".join(f"{SKILL_CN[k]}{int(pool[k])}" for k in SKILL_KEYS_LOW)
    print(f"合并总属性池: {sk_str}")
    print("推荐上阵厨师（按位置顺序）:")
    for i, st in enumerate(sts, 1):
        ch = st["chef"]
        eq_nm = st["equip"]["name"] if st["equip"] else "无"
        print(f"  [位置{i}] {ch['name']} ({ch['rarity']}火) | 厨具: {eq_nm}")
        print(f"         生效技能: {describe_chef_buffs(st)}")
    print("各菜品预估得分:")
    for d in det:
        print(
            f"  - {d['recipe']} ({d['rarity']}火/{d['grade']}, {d['ratio']:.1f}倍) 底价{d['base']} "
            f"| 基础售价+{d['basic_pct']:.0f}% 总倍率{d['total_buff']:.0f}% => {d['score']:,}"
        )


def self_test_dvmvgd(ctx, solver):
    by_name = {c["name"]: c["id"] for c in ctx.chefs_by_id.values()}
    # Floor 1 calibration check
    d1 = solver.resolve_dishes(["香菇青菜", "扬州炒饭", "地三鲜", "回锅肉", "海鲜面"])
    sc1, _, det1, _ = solver.evaluate_team([by_name["丹叙"], by_name["吕布"], by_name["朱英台"]], d1)
    assert [d["score"] for d in det1] == [541, 1102, 1740, 4160, 2617] and sc1 == 10160
    # Floor 2 calibration check
    d2 = solver.resolve_dishes(["鸡肉蔬菜沙拉", "蟹壳黄", "酒香草头", "面茶", "蛤蜊蒸蛋", "串烤盐焗虾"])
    sc2, _, _, _ = solver.evaluate_team([by_name["炎罗"], by_name["巴克比"], by_name["孔布明"]], d2)
    assert sc2 == 13528, f"Floor 2 偏差: {sc2} != 13528"
    # Floor 3 calibration check
    d3 = solver.resolve_dishes(["冰淇淋鸡蛋仔", "芋泥香酥鸭", "珍珠丸子", "八宝辣酱", "青椒塞肉", "泡鲁达"])
    sc3, _, _, _ = solver.evaluate_team([by_name["悲歌"], by_name["舒婷"], by_name["葛丽叶"], by_name["起司"]], d3)
    assert sc3 == 49125, f"Floor 3 偏差: {sc3} != 49125"
    print(f"[三层校准校验通过] 第1层={sc1:,} | 第2层={sc2:,} | 第3层={sc3:,} (全部 0 误差!)")


def main():
    parser = argparse.ArgumentParser(description="爆炒江湖《百味楼》配队求解器（0误差校准版）")
    parser.add_argument("--token", required=True, help="白菜菊花校验码")
    parser.add_argument("--dishes", required=True, help="逗号分隔的 5 道菜名")
    parser.add_argument("--slots", type=int, default=3, help="本层最多上阵厨师数")
    parser.add_argument("--target", type=int, default=0, help="本层目标分数")
    parser.add_argument("--swap-equips", action="store_true", help="允许从已有厨具池中换厨具")
    parser.add_argument("--budget", action="store_true", help="同时给出省主力（<=4火）低配过线方案")
    parser.add_argument("--exclude", default="", help="逗号分隔的排除厨师名（如已在其他层锁定）")
    parser.add_argument("--self-test", action="store_true", help="运行 DVMVGD 实测 0 误差校验")
    args = parser.parse_args()

    gd = load_or_fetch(os.path.join(DATA_DIR, "data.min.json"), DATA_URL)
    ua = load_or_fetch(os.path.join(DATA_DIR, f"user_{args.token}.json"), ARCHIVE_URL.format(token=args.token))
    ctx = GameContext(gd, ua)
    solver = BaiweilouSolver(ctx)

    if args.self_test and args.token == "DVMVGD":
        self_test_dvmvgd(ctx, solver)

    dishes = solver.resolve_dishes(args.dishes.split(","))
    ex_names = [x.strip() for x in args.exclude.split(",") if x.strip()]
    by_name = {c["name"]: c["id"] for c in ctx.chefs_by_id.values()}
    ex_ids = {by_name[nm] for nm in ex_names if nm in by_name}

    sc1, res1 = solver.solve(dishes, slots=args.slots, target=args.target, swap_equips=False, exclude_ids=ex_ids)
    print_baiweilou_result(f"百味楼（{args.slots}人 / 不换厨具最高分）", sc1, args.target, res1)

    if args.swap_equips:
        sc2, res2 = solver.solve(dishes, slots=args.slots, target=args.target, swap_equips=True, exclude_ids=ex_ids)
        print_baiweilou_result(f"百味楼（{args.slots}人 / 换厨具极限分）", sc2, args.target, res2)

    if args.budget:
        sc3, res3 = solver.solve(dishes, slots=args.slots, target=args.target, swap_equips=False, exclude_ids=ex_ids, max_rarity=4)
        print_baiweilou_result(f"百味楼（{args.slots}人 / 省5火主力方案）", sc3, args.target, res3)


if __name__ == "__main__":
    main()
