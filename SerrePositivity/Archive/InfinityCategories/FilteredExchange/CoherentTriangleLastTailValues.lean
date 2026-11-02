module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleLastTailHead
/-!
概要：最大化側の最後辺の tail を、元の恒等射・最後射・恒等射へ揃える。
方針：同じ strict な順序図式の正頂点ラベルで Hom の定値値を計算する。
規約：全次数の元の path と対象を保持する。
使われ方：Ncomp の実単体の tail 全体の一致。
-/

@[expose] public section
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：指定時刻の同じ tail の表示を回収する。方針：元のラベルで計算する。
規約：元の対象と全 Hom を保持。使われ方：実 tail の一致。 -/
lemma coherentTriangleLastTailOrder_succ_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i : Fin (n + 1)) (hi : α.toOrderHom i = 0) :
    coherentTriangleLastTailOrder α (ULift.up i.succ) = (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) := by
  change ULift.up (α.toOrderHom i).succ = _
  rw [hi]
  rfl
/-- 概要：指定時刻の同じ tail の表示を回収する。方針：元のラベルで計算する。
規約：元の対象と全 Hom を保持。使われ方：実 tail の一致。 -/
lemma coherentTriangleLastTailOrder_succ_one {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i : Fin (n + 1)) (hi : α.toOrderHom i = 1) :
    coherentTriangleLastTailOrder α (ULift.up i.succ) = (ULift.up (2 : Fin 3) : ULift.{u} (Fin 3)) := by
  change ULift.up (α.toOrderHom i).succ = _
  rw [hi]
  rfl
/-- 概要：指定時刻の同じ tail の表示を回収する。方針：元のラベルで計算する。
規約：元の対象と全 Hom を保持。使われ方：実 tail の一致。 -/
lemma coherentTriangleLastTail_tail_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : α.toOrderHom i = 0) (hj : α.toOrderHom j = 0) :
    (coherentTriangleLastTail s α).val.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastTail_obj_zero s α i hi) (coherentTriangleLastTail_obj_zero s α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (𝟙 (s.obj ⟨ULift.up 1⟩))) := by
  have h := coherentTriangleLastTail_map_labels s α (ULift.up i.succ) (ULift.up j.succ)
    (Fin.succ_le_succ_iff.mpr hij) (ULift.up 1) (ULift.up 1)
    (coherentTriangleLastTailOrder_succ_zero α i hi)
    (coherentTriangleLastTailOrder_succ_zero α j hj) (by decide)
  change _ = SSet.const (SimplicialCategory.homEquiv' _ _
    ((coherentSimplexStrictDiagram s).map (𝟙 (ULift.up (1 : Fin 3))))) at h
  rw [(coherentSimplexStrictDiagram s).map_id (ULift.up (1 : Fin 3))] at h
  convert h using 1 <;> rfl
/-- 概要：指定時刻の同じ tail の表示を回収する。方針：元のラベルで計算する。
規約：元の対象と全 Hom を保持。使われ方：実 tail の一致。 -/
lemma coherentTriangleLastTail_tail_one {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : α.toOrderHom i = 1) (hj : α.toOrderHom j = 1) :
    (coherentTriangleLastTail s α).val.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastTail_obj_one s α i hi) (coherentTriangleLastTail_obj_one s α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (𝟙 (s.obj ⟨ULift.up 2⟩))) := by
  have h := coherentTriangleLastTail_map_labels s α (ULift.up i.succ) (ULift.up j.succ)
    (Fin.succ_le_succ_iff.mpr hij) (ULift.up 2) (ULift.up 2)
    (coherentTriangleLastTailOrder_succ_one α i hi)
    (coherentTriangleLastTailOrder_succ_one α j hj) (by decide)
  change _ = SSet.const (SimplicialCategory.homEquiv' _ _
    ((coherentSimplexStrictDiagram s).map (𝟙 (ULift.up (2 : Fin 3))))) at h
  rw [(coherentSimplexStrictDiagram s).map_id (ULift.up (2 : Fin 3))] at h
  convert h using 1 <;> rfl
/-- 概要：指定時刻の同じ tail の表示を回収する。方針：元のラベルで計算する。
規約：元の対象と全 Hom を保持。使われ方：実 tail の一致。 -/
lemma coherentTriangleLastTail_tail_mixed {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : α.toOrderHom i = 0) (hj : α.toOrderHom j = 1) :
    (coherentTriangleLastTail s α).val.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentTriangleLastTail_obj_zero s α i hi) (coherentTriangleLastTail_obj_one s α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (coherentEdgeHom (SpaceInfinity.δ 0 s))) := by
  have h := coherentTriangleLastTail_map_labels s α (ULift.up i.succ) (ULift.up j.succ)
    (Fin.succ_le_succ_iff.mpr hij) (ULift.up 1) (ULift.up 2)
    (coherentTriangleLastTailOrder_succ_zero α i hi)
    (coherentTriangleLastTailOrder_succ_one α j hj) (by decide)
  rw [coherentSimplexStrictDiagram_last_arrow s] at h
  exact h
end SerrePositivity.InfinityCategories.F2
