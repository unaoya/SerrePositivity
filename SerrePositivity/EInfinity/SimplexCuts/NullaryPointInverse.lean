module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointMark
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalEdgeRanks

/-!
# nullaryの元の一頂点区間の挿入・削除の両逆

Berger–Fresse §1.1.3・§2.2.6、M14 L12a の有限対応、報告 §318・§322。
元の水平辺の昇順番号・同じ指定頂点・既存の水平辺の同値を保って全Cutを対応させる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 挿入後の同じ昇順番号の水平辺は、元の指定挿入辺（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_edge {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    cutHorizontalEdge (nullaryPointInsertCut t p)
      ⟨min p.val m, by have h := Nat.min_le_right p.val m; omega⟩ =
        nullaryPointInsertionEdge t p := by
  let S := nullaryPointInsertCut t p
  let a := nullaryPointInsertionEdge t p
  let z := horizontalBoundaryFaceEquiv m q (p, t)
  have ha : a ∈ S.val := (BarrattEccles.horizontalInsertionEquiv m q a t).property
  have hh := horizontalBoundaryFaceEquiv_horizontal m q (p, t)
  rw [← nullaryPointInsertCut_eq_horizontalBoundaryFace] at hh
  change S.horizontal z.val.2 = p at hh
  have hm := nullaryPointInsertionEdge_mark_val t p
  change z.val.2.val = a.val + if p.val = m + 1 then 1 else 0 at hm
  apply cutHorizontalEdge_eq_of_horizontal S a ha
  apply Fin.ext
  change (S.horizontal a.castSucc).val = min p.val m
  by_cases hlast : p.val = m + 1
  · rw [ite_eq_left hlast] at hm
    have hz : z.val.2 = a.succ := Fin.ext hm
    rw [hz] at hh
    have hs := (S.step_of_mem a ha).1
    have hv := congrArg (fun j : Fin (m + 2) => j.val) hh
    have hmin : min p.val m = m := Nat.min_eq_right (by omega)
    omega
  · have hm0 : z.val.2.val = a.val := by
      simpa only [ite_eq_right hlast, Nat.add_zero] using hm
    have hz : z.val.2 = a.castSucc := Fin.ext hm0
    rw [hz] at hh
    have hv := congrArg (fun j : Fin (m + 2) => j.val) hh
    have hp := p.isLt
    have hmin : min p.val m = p.val := Nat.min_eq_left (by omega)
    omega

/-- 同じ元の削除辺の等式は、所属証明を保って同じ逆写像を与える（BF §1.1.3）。 -/
lemma horizontalInsertionEquiv_symm_congr {m q : ℕ} (s : Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (ha : a ∈ s.val) (hb : b ∈ s.val) (h : a = b) :
    (BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩ =
      (BarrattEccles.horizontalInsertionEquiv m q b).symm ⟨s, hb⟩ := by
  subst b
  rfl

/-- 元の同じ挿入辺を削除すると、小さいCutそのものへ戻る（BF §2.2.6）。 -/
lemma nullaryPointEraseCut_insert {m q : ℕ} (t : Cut m q) (p : Fin (m + 2)) :
    nullaryPointEraseCut (nullaryPointInsertCut t p) p = t := by
  unfold nullaryPointEraseCut
  dsimp only
  have h := horizontalInsertionEquiv_symm_congr (nullaryPointInsertCut t p) _ _
    ((nullaryPointInsertCut t p).val.orderEmbOfFin_mem (nullaryPointInsertCut t p).property _)
    (BarrattEccles.horizontalInsertionEquiv m q (nullaryPointInsertionEdge t p) t).property
    (nullaryPointInsertCut_edge t p)
  exact h.trans ((BarrattEccles.horizontalInsertionEquiv m q
    (nullaryPointInsertionEdge t p)).symm_apply_apply t)

/-- 元の一頂点の区間は、既存の同じ水平境界の逆で全て得られる（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_surjective {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) : ∃ t : Cut m q, nullaryPointInsertCut t p = s := by
  let j := (intervalPositions s p).min' (intervalPositions_nonempty s p)
  have hj : s.horizontal j = p := (Finset.mem_filter.mp
    ((intervalPositions s p).min'_mem (intervalPositions_nonempty s p))).2
  have hk : boundaryVertexKind s j = .horizontal := by
    apply (boundaryVertexKind_eq_horizontal_gap s j).mpr
    refine ⟨by omega, ?_⟩
    rw [hj, h, Nat.sub_self]
  let z : BoundaryVertexOfKind (m + 1) q .horizontal := ⟨⟨s, j⟩, hk⟩
  generalize hpre : (horizontalBoundaryFaceEquiv m q).symm z = c
  have he : horizontalBoundaryFaceEquiv m q c = z := by
    rw [← hpre]
    exact (horizontalBoundaryFaceEquiv m q).apply_symm_apply z
  have hp := horizontalBoundaryFaceEquiv_horizontal m q c
  rw [he] at hp
  change s.horizontal j = c.1 at hp
  have hc : c.1 = p := hp.symm.trans hj
  have hs := congrArg (fun z : BoundaryVertexOfKind (m + 1) q .horizontal => z.val.1) he
  refine ⟨c.2, ?_⟩
  rw [nullaryPointInsertCut_eq_horizontalBoundaryFace]
  change (horizontalBoundaryFaceEquiv m q (c.1, c.2)).val.1 = s at hs
  rw [hc] at hs
  exact hs

/-- 元の一頂点を削除して挿入し直すと、同じ大きいCutへ戻る（BF §2.2.6）。 -/
lemma nullaryPointInsertCut_erase {m q : ℕ} (s : Cut (m + 1) q) (p : Fin (m + 2))
    (h : hi s p = lo s p) :
    nullaryPointInsertCut (nullaryPointEraseCut s p) p = s := by
  obtain ⟨t, ht⟩ := nullaryPointInsertCut_surjective s p h
  rw [← ht, nullaryPointEraseCut_insert]

/-- 元の一頂点区間を消すnullaryの全Cutの同値（BF §2.2.6）。 -/
def nullaryPointCutEquiv (m q : ℕ) (p : Fin (m + 2)) :
    Cut m q ≃ {s : Cut (m + 1) q // hi s p = lo s p} where
  toFun t := ⟨nullaryPointInsertCut t p, nullaryPointInsertCut_hi_eq_lo t p⟩
  invFun s := nullaryPointEraseCut s.val p
  left_inv t := nullaryPointEraseCut_insert t p
  right_inv s := Subtype.ext (nullaryPointInsertCut_erase s.val p s.property)

end SerrePositivity.EInfinity.SimplexCuts
