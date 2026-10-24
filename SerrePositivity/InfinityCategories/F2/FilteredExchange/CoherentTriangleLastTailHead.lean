module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastTail
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.MorphismInitialHeadCoordinates
/-!
概要：最大化側の最後辺の初点固定 tail の head を、元の第一射と二辺合成へ戻す。
方針：同じ strict な順序図式の零時刻と一時刻のラベルを計算する。
規約：元の始点と全 Hom を保持する。
使われ方：Ncomp の全係数における head の合成則の照合。
-/

@[expose] public section
noncomputable section
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：零時刻の対象は元の中間対象。方針：同じ時刻のラベルを計算する。
規約：元の対象と射を保持。使われ方：最後辺の全係数の照合。 -/
lemma coherentTriangleLastTail_obj_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    (coherentTriangleLastTail s α).val.obj ⟨ULift.up j.succ⟩ = s.obj ⟨ULift.up 1⟩ := by
  change s.obj ⟨ULift.up (α.toOrderHom j).succ⟩ = _
  rw [hj]
  rfl
/-- 概要：一時刻の対象は元の終対象。方針：同じ時刻のラベルを計算する。
規約：元の対象と射を保持。使われ方：最後辺の全係数の照合。 -/
lemma coherentTriangleLastTail_obj_one {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    (coherentTriangleLastTail s α).val.obj ⟨ULift.up j.succ⟩ = s.obj ⟨ULift.up 2⟩ := by
  change s.obj ⟨ULift.up (α.toOrderHom j).succ⟩ = _
  rw [hj]
  rfl
/-- 概要：零時刻の head は元の第一射の定値射。方針：同じ時刻のラベルを計算する。
規約：元の対象と射を保持。使われ方：最後辺の全係数の照合。 -/
lemma coherentTriangleLastTail_head_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    (coherentTriangleLastTail s α).val.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (coherentTriangleLastTail_obj_zero s α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (coherentEdgeHom (SpaceInfinity.δ 2 s))) := by
  have hl : coherentTriangleLastTailOrder α (ULift.up j.succ) =
      (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) := by
    change ULift.up (α.toOrderHom j).succ = _
    rw [hj]
    rfl
  have h := coherentTriangleLastTail_map_labels s α (ULift.up 0) (ULift.up j.succ)
    (show (0 : Fin (n + 2)) ≤ j.succ from Fin.zero_le _) (ULift.up 0) (ULift.up 1)
    rfl hl (by decide)
  rw [coherentSimplexStrictDiagram_first_arrow] at h
  exact h
/-- 概要：一時刻の head は元の二辺合成の定値射。方針：同じ時刻のラベルを計算する。
規約：元の対象と射を保持。使われ方：最後辺の全係数の照合。 -/
lemma coherentTriangleLastTail_head_one {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    (coherentTriangleLastTail s α).val.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (coherentTriangleLastTail_obj_one s α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' _ _
        (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s))) := by
  have hl : coherentTriangleLastTailOrder α (ULift.up j.succ) =
      (ULift.up (2 : Fin 3) : ULift.{u} (Fin 3)) := by
    change ULift.up (α.toOrderHom j).succ = _
    rw [hj]
    rfl
  have h := coherentTriangleLastTail_map_labels s α (ULift.up 0) (ULift.up j.succ)
    (show (0 : Fin (n + 2)) ≤ j.succ from Fin.zero_le _) (ULift.up 0) (ULift.up 2)
    rfl hl (by decide)
  rw [coherentSimplexStrictDiagram_composite_arrow] at h
  exact h
end SerrePositivity.InfinityCategories.F2
