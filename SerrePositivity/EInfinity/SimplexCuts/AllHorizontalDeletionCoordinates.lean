module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalFaceCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLastFace
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
# 全水平境界同値の指定削除座標

Berger–Fresse §2.2.7、M14 L09a。
始点・内部・終点の既存座標を同じ有限同値に沿って貼り合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C248：既存の全水平同値が指定する切断と頂点における両座標の削除式。 -/
lemma horizontalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (m + 2) × Cut m q) (l : Fin (m + q + 1)) :
    let z := (horizontalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.1.succAbove (c.2.horizontal l) ∧
      z.1.vertical (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        c.2.vertical l := by
  let P (z : MarkedCut (m + 1) q) (a : Fin (m + 2)) (t : Cut m q) : Prop :=
    z.1.horizontal (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        a.succAbove (t.horizontal l) ∧
      z.1.vertical (z.2.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        t.vertical l
  have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
  change P (horizontalBoundaryFaceEquiv m q c).val c.1 c.2
  obtain ⟨z, rfl⟩ := (coefficientIndexEndpointEquiv m q).symm.surjective c
  rcases z with t | ⟨t, i⟩ | t
  · rw [coefficientIndexEndpointEquiv_symm_first, horizontalBoundaryFaceEquiv_first]
    dsimp only [P]
    let e := BarrattEccles.horizontalInsertionEquiv m q 0
    have hs : e.symm ⟨(e t).val, (e t).property⟩ = t := e.symm_apply_apply t
    dsimp only [e] at hs
    change (e t).val.horizontal ((0 : Fin (m + 1 + q + 1)).succAbove (Fin.cast _ l)) =
        (0 : Fin (m + 2)).succAbove (t.horizontal l) ∧
      (e t).val.vertical ((0 : Fin (m + 1 + q + 1)).succAbove (Fin.cast _ l)) = t.vertical l
    constructor
    · simpa only [e, Equiv.symm_apply_apply, hs, hc, Fin.succAbove_zero] using
        BarrattEccles.horizontalDeletion_first_horizontal (e t).val (e t).property
          (Fin.cast (by omega) l)
    · simpa only [e, Equiv.symm_apply_apply, hs, hc, Fin.succAbove_zero] using
        BarrattEccles.horizontalDeletion_first_vertical (e t).val (e t).property
          (Fin.cast (by omega) l)
  · rw [coefficientIndexEndpointEquiv_symm_interior, horizontalBoundaryFaceEquiv_interior]
    dsimp only [P]
    let b := BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i)
    let a : Fin (m + 1 + q) := Fin.cast (by omega : m + q + 1 = m + 1 + q) b.val.2.castSucc
    let a' : Fin (m + 1 + q) := Fin.cast (by omega : m + q + 1 = m + 1 + q) b.val.2.succ
    let e := BarrattEccles.horizontalInsertionEquiv m q a
    have ha : a ∈ (e t).val.val := (e t).property
    have hb : a' ∈ (e t).val.val := (BarrattEccles.horizontalCornerEquiv m q b).property.2
    have hs : e.symm ⟨(e t).val, ha⟩ = t := e.symm_apply_apply t
    have hh : (e t).val.horizontal a.succ = i.castSucc.succ :=
      horizontalInteriorFaceEquiv_horizontal m q t i
    dsimp only [e] at hs
    change (e t).val.horizontal (a.succ.succAbove (Fin.cast _ l)) =
        i.castSucc.succ.succAbove (t.horizontal l) ∧
      (e t).val.vertical (a.succ.succAbove (Fin.cast _ l)) = t.vertical l
    constructor
    · have ht := BarrattEccles.horizontalDeletion_horizontal (e t).val a a' (by rfl) ha hb
        (Fin.cast (by omega) l)
      simpa only [e, Equiv.symm_apply_apply, hs, hh, hc] using ht
    · have ht := BarrattEccles.horizontalDeletion_vertical (e t).val a ha (Fin.cast (by omega) l)
      simpa only [e, Equiv.symm_apply_apply, hs, hc] using ht
  · rw [coefficientIndexEndpointEquiv_symm_last, horizontalBoundaryFaceEquiv_last]
    dsimp only [P]
    let a : Fin (m + 1 + q) := ⟨m + q, by omega⟩
    let e := BarrattEccles.horizontalInsertionEquiv m q a
    have hs : e.symm ⟨(e t).val, (e t).property⟩ = t := e.symm_apply_apply t
    have hk : a.succ = Fin.last (m + 1 + q) := Fin.ext (by dsimp [a]; omega)
    dsimp only [e] at hs
    change (e t).val.horizontal ((Fin.last (m + 1 + q)).succAbove (Fin.cast _ l)) =
        (Fin.last (m + 1)).succAbove (t.horizontal l) ∧
      (e t).val.vertical ((Fin.last (m + 1 + q)).succAbove (Fin.cast _ l)) = t.vertical l
    constructor
    · have ht := BarrattEccles.horizontalDeletion_last (e t).val a (e t).property
        (by dsimp [a]; omega) (Fin.cast (by omega) l)
      simpa only [e, Equiv.symm_apply_apply, hs, hk, hc] using ht
    · have ht := BarrattEccles.horizontalDeletion_vertical (e t).val a (e t).property
        (Fin.cast (by omega) l)
      simpa only [e, Equiv.symm_apply_apply, hs, hk, hc] using ht

end SerrePositivity.EInfinity.SimplexCuts
