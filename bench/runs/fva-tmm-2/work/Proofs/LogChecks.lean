import Proofs.Data

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem log_1 : (Data.logI 1).Holds (Real.log (1 : Nat)) := by
  apply log_nat 1 0 (-1 / 1000000000000 : ℚ) (1 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_2 : (Data.logI 2).Holds (Real.log (2 : Nat)) := by
  apply log_nat 2 1 (346573590279 / 500000000000 : ℚ) (693147180561 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_3 : (Data.logI 3).Holds (Real.log (3 : Nat)) := by
  apply log_nat 3 1 (1098612288667 / 1000000000000 : ℚ) (109861228867 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_4 : (Data.logI 4).Holds (Real.log (4 : Nat)) := by
  apply log_nat 4 2 (693147180559 / 500000000000 : ℚ) (1386294361121 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_5 : (Data.logI 5).Holds (Real.log (5 : Nat)) := by
  apply log_nat 5 2 (1609437912433 / 1000000000000 : ℚ) (402359478109 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_6 : (Data.logI 6).Holds (Real.log (6 : Nat)) := by
  apply log_nat 6 2 (1791759469227 / 1000000000000 : ℚ) (179175946923 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_7 : (Data.logI 7).Holds (Real.log (7 : Nat)) := by
  apply log_nat 7 2 (972955074527 / 500000000000 : ℚ) (1945910149057 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_8 : (Data.logI 8).Holds (Real.log (8 : Nat)) := by
  apply log_nat 8 3 (1039720770839 / 500000000000 : ℚ) (2079441541681 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_9 : (Data.logI 9).Holds (Real.log (9 : Nat)) := by
  apply log_nat 9 3 (439444915467 / 200000000000 : ℚ) (1098612288669 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_10 : (Data.logI 10).Holds (Real.log (10 : Nat)) := by
  apply log_nat 10 3 (2302585092993 / 1000000000000 : ℚ) (575646273249 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_11 : (Data.logI 11).Holds (Real.log (11 : Nat)) := by
  apply log_nat 11 3 (2397895272797 / 1000000000000 : ℚ) (2997369091 / 1250000000 : ℚ)
  all_goals decide +kernel

theorem log_12 : (Data.logI 12).Holds (Real.log (12 : Nat)) := by
  apply log_nat 12 3 (2484906649787 / 1000000000000 : ℚ) (248490664979 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_13 : (Data.logI 13).Holds (Real.log (13 : Nat)) := by
  apply log_nat 13 3 (128247467873 / 50000000000 : ℚ) (2564949357463 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_14 : (Data.logI 14).Holds (Real.log (14 : Nat)) := by
  apply log_nat 14 3 (1319528664807 / 500000000000 : ℚ) (2639057329617 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_15 : (Data.logI 15).Holds (Real.log (15 : Nat)) := by
  apply log_nat 15 3 (2708050201101 / 1000000000000 : ℚ) (169253137569 / 62500000000 : ℚ)
  all_goals decide +kernel

theorem log_16 : (Data.logI 16).Holds (Real.log (16 : Nat)) := by
  apply log_nat 16 4 (1386294361119 / 500000000000 : ℚ) (2772588722241 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_17 : (Data.logI 17).Holds (Real.log (17 : Nat)) := by
  apply log_nat 17 4 (566642668811 / 200000000000 : ℚ) (1416606672029 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_18 : (Data.logI 18).Holds (Real.log (18 : Nat)) := by
  apply log_nat 18 4 (578074351579 / 200000000000 : ℚ) (1445185878949 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_19 : (Data.logI 19).Holds (Real.log (19 : Nat)) := by
  apply log_nat 19 4 (588887795833 / 200000000000 : ℚ) (92013718099 / 31250000000 : ℚ)
  all_goals decide +kernel

theorem log_20 : (Data.logI 20).Holds (Real.log (20 : Nat)) := by
  apply log_nat 20 4 (187233267097 / 62500000000 : ℚ) (599146454711 / 200000000000 : ℚ)
  all_goals decide +kernel

theorem log_21 : (Data.logI 21).Holds (Real.log (21 : Nat)) := by
  apply log_nat 21 4 (1522261218861 / 500000000000 : ℚ) (121780897509 / 40000000000 : ℚ)
  all_goals decide +kernel

theorem log_22 : (Data.logI 22).Holds (Real.log (22 : Nat)) := by
  apply log_nat 22 4 (3091042453357 / 1000000000000 : ℚ) (38638030667 / 12500000000 : ℚ)
  all_goals decide +kernel

theorem log_23 : (Data.logI 23).Holds (Real.log (23 : Nat)) := by
  apply log_nat 23 4 (391936776991 / 125000000000 : ℚ) (3135494215931 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_24 : (Data.logI 24).Holds (Real.log (24 : Nat)) := by
  apply log_nat 24 4 (1589026915173 / 500000000000 : ℚ) (3178053830349 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_25 : (Data.logI 25).Holds (Real.log (25 : Nat)) := by
  apply log_nat 25 4 (3218875824867 / 1000000000000 : ℚ) (321887582487 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_26 : (Data.logI 26).Holds (Real.log (26 : Nat)) := by
  apply log_nat 26 4 (162904826901 / 50000000000 : ℚ) (3258096538023 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_27 : (Data.logI 27).Holds (Real.log (27 : Nat)) := by
  apply log_nat 27 4 (3295836866003 / 1000000000000 : ℚ) (1647918433003 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_28 : (Data.logI 28).Holds (Real.log (28 : Nat)) := by
  apply log_nat 28 4 (1666102255087 / 500000000000 : ℚ) (3332204510177 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_29 : (Data.logI 29).Holds (Real.log (29 : Nat)) := by
  apply log_nat 29 4 (673459165997 / 200000000000 : ℚ) (841823957497 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_30 : (Data.logI 30).Holds (Real.log (30 : Nat)) := by
  apply log_nat 30 4 (3401197381661 / 1000000000000 : ℚ) (106287418177 / 31250000000 : ℚ)
  all_goals decide +kernel

theorem log_31 : (Data.logI 31).Holds (Real.log (31 : Nat)) := by
  apply log_nat 31 4 (858496801121 / 250000000000 : ℚ) (3433987204487 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_32 : (Data.logI 32).Holds (Real.log (32 : Nat)) := by
  apply log_nat 32 5 (1732867951399 / 500000000000 : ℚ) (3465735902801 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_33 : (Data.logI 33).Holds (Real.log (33 : Nat)) := by
  apply log_nat 33 5 (699301512293 / 200000000000 : ℚ) (874126890367 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_34 : (Data.logI 34).Holds (Real.log (34 : Nat)) := by
  apply log_nat 34 5 (705272104923 / 200000000000 : ℚ) (1763180262309 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_35 : (Data.logI 35).Holds (Real.log (35 : Nat)) := by
  apply log_nat 35 5 (222209253843 / 62500000000 : ℚ) (3555348061491 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_36 : (Data.logI 36).Holds (Real.log (36 : Nat)) := by
  apply log_nat 36 5 (716703787691 / 200000000000 : ℚ) (1791759469229 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_37 : (Data.logI 37).Holds (Real.log (37 : Nat)) := by
  apply log_nat 37 5 (3610917912643 / 1000000000000 : ℚ) (1805458956323 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_38 : (Data.logI 38).Holds (Real.log (38 : Nat)) := by
  apply log_nat 38 5 (145503446389 / 40000000000 : ℚ) (227349134983 / 62500000000 : ℚ)
  all_goals decide +kernel

theorem log_39 : (Data.logI 39).Holds (Real.log (39 : Nat)) := by
  apply log_nat 39 5 (228972602883 / 62500000000 : ℚ) (3663561646131 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_40 : (Data.logI 40).Holds (Real.log (40 : Nat)) := by
  apply log_nat 40 5 (115277482941 / 31250000000 : ℚ) (737775890823 / 200000000000 : ℚ)
  all_goals decide +kernel

theorem log_41 : (Data.logI 41).Holds (Real.log (41 : Nat)) := by
  apply log_nat 41 5 (3713572066703 / 1000000000000 : ℚ) (1856786033353 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_42 : (Data.logI 42).Holds (Real.log (42 : Nat)) := by
  apply log_nat 42 5 (1868834809141 / 500000000000 : ℚ) (747533923657 / 200000000000 : ℚ)
  all_goals decide +kernel

theorem log_621 : (Data.logI 621).Holds (Real.log (621 : Nat)) := by
  apply log_nat 621 9 (1607832770483 / 250000000000 : ℚ) (1286266216387 / 200000000000 : ℚ)
  all_goals decide +kernel

theorem log_755 : (Data.logI 755).Holds (Real.log (755 : Nat)) := by
  apply log_nat 755 9 (1617851013 / 244140625 : ℚ) (6626717749251 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1097 : (Data.logI 1097).Holds (Real.log (1097 : Nat)) := by
  apply log_nat 1097 10 (3500167230137 / 500000000000 : ℚ) (7000334460277 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1136 : (Data.logI 1136).Holds (Real.log (1136 : Nat)) := by
  apply log_nat 1136 10 (87940857491 / 12500000000 : ℚ) (7035268599283 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1219 : (Data.logI 1219).Holds (Real.log (1219 : Nat)) := by
  apply log_nat 1219 10 (177644653237 / 25000000000 : ℚ) (7105786129483 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1261 : (Data.logI 1261).Holds (Real.log (1261 : Nat)) := by
  apply log_nat 1261 10 (7139660335963 / 1000000000000 : ℚ) (3569830167983 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_1916 : (Data.logI 1916).Holds (Real.log (1916 : Nat)) := by
  apply log_nat 1916 10 (7557994958529 / 1000000000000 : ℚ) (1889498739633 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_815784 : (Data.logI 815784).Holds (Real.log (815784 : Nat)) := by
  apply log_nat 815784 19 (6805952446511 / 500000000000 : ℚ) (544476195721 / 40000000000 : ℚ)
  all_goals decide +kernel

theorem log_815787 : (Data.logI 815787).Holds (Real.log (815787 : Nat)) := by
  apply log_nat 815787 19 (13611908570459 / 1000000000000 : ℚ) (6805954285231 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_932436 : (Data.logI 932436).Holds (Real.log (932436 : Nat)) := by
  apply log_nat 932436 19 (3436388948859 / 250000000000 : ℚ) (13745555795439 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_932439 : (Data.logI 932439).Holds (Real.log (932439 : Nat)) := by
  apply log_nat 932439 19 (13745559012809 / 1000000000000 : ℚ) (3436389753203 / 250000000000 : ℚ)
  all_goals decide +kernel

theorem log_956410 : (Data.logI 956410).Holds (Real.log (956410 : Nat)) := by
  apply log_nat 956410 19 (6885470985193 / 500000000000 : ℚ) (13770941970389 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_956413 : (Data.logI 956413).Holds (Real.log (956413 : Nat)) := by
  apply log_nat 956413 19 (13770945107111 / 1000000000000 : ℚ) (6885472553557 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_958279 : (Data.logI 958279).Holds (Real.log (958279 : Nat)) := by
  apply log_nat 958279 19 (2754578849257 / 200000000000 : ℚ) (860805890393 / 62500000000 : ℚ)
  all_goals decide +kernel

theorem log_958282 : (Data.logI 958282).Holds (Real.log (958282 : Nat)) := by
  apply log_nat 958282 19 (3443224344223 / 250000000000 : ℚ) (2754579475379 / 200000000000 : ℚ)
  all_goals decide +kernel

theorem log_975526 : (Data.logI 975526).Holds (Real.log (975526 : Nat)) := by
  apply log_nat 975526 19 (13790732091687 / 1000000000000 : ℚ) (1379073209169 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_975529 : (Data.logI 975529).Holds (Real.log (975529 : Nat)) := by
  apply log_nat 975529 19 (6895367583473 / 500000000000 : ℚ) (13790735166949 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1000000 : (Data.logI 1000000).Holds (Real.log (1000000 : Nat)) := by
  apply log_nat 1000000 19 (13815510557963 / 1000000000000 : ℚ) (6907755278983 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_1147753 : (Data.logI 1147753).Holds (Real.log (1147753 : Nat)) := by
  apply log_nat 1147753 20 (3488329168979 / 250000000000 : ℚ) (13953316675919 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1147756 : (Data.logI 1147756).Holds (Real.log (1147756 : Nat)) := by
  apply log_nat 1147756 20 (3488329822429 / 250000000000 : ℚ) (13953319289719 / 1000000000000 : ℚ)
  all_goals decide +kernel

theorem log_1281082 : (Data.logI 1281082).Holds (Real.log (1281082 : Nat)) := by
  apply log_nat 1281082 20 (14063215591319 / 1000000000000 : ℚ) (7031607795661 / 500000000000 : ℚ)
  all_goals decide +kernel

theorem log_1281085 : (Data.logI 1281085).Holds (Real.log (1281085 : Nat)) := by
  apply log_nat 1281085 20 (14063217933087 / 1000000000000 : ℚ) (1406321793309 / 100000000000 : ℚ)
  all_goals decide +kernel

theorem log_valid (n : Nat) (hn : n ∈ Data.logged) :
    (Data.logI n).Holds (Real.log n) := by
  simp only [Data.logged, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n; exact log_1
  · subst n; exact log_2
  · subst n; exact log_3
  · subst n; exact log_4
  · subst n; exact log_5
  · subst n; exact log_6
  · subst n; exact log_7
  · subst n; exact log_8
  · subst n; exact log_9
  · subst n; exact log_10
  · subst n; exact log_11
  · subst n; exact log_12
  · subst n; exact log_13
  · subst n; exact log_14
  · subst n; exact log_15
  · subst n; exact log_16
  · subst n; exact log_17
  · subst n; exact log_18
  · subst n; exact log_19
  · subst n; exact log_20
  · subst n; exact log_21
  · subst n; exact log_22
  · subst n; exact log_23
  · subst n; exact log_24
  · subst n; exact log_25
  · subst n; exact log_26
  · subst n; exact log_27
  · subst n; exact log_28
  · subst n; exact log_29
  · subst n; exact log_30
  · subst n; exact log_31
  · subst n; exact log_32
  · subst n; exact log_33
  · subst n; exact log_34
  · subst n; exact log_35
  · subst n; exact log_36
  · subst n; exact log_37
  · subst n; exact log_38
  · subst n; exact log_39
  · subst n; exact log_40
  · subst n; exact log_41
  · subst n; exact log_42
  · subst n; exact log_621
  · subst n; exact log_755
  · subst n; exact log_1097
  · subst n; exact log_1136
  · subst n; exact log_1219
  · subst n; exact log_1261
  · subst n; exact log_1916
  · subst n; exact log_815784
  · subst n; exact log_815787
  · subst n; exact log_932436
  · subst n; exact log_932439
  · subst n; exact log_956410
  · subst n; exact log_956413
  · subst n; exact log_958279
  · subst n; exact log_958282
  · subst n; exact log_975526
  · subst n; exact log_975529
  · subst n; exact log_1000000
  · subst n; exact log_1147753
  · subst n; exact log_1147756
  · subst n; exact log_1281082
  · subst n; exact log_1281085

end Proofs
