module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismPrismSimplices

/-!
概要：元の全係数 cone 単体の正頂点間 Hom を、同じ元の恒等射・指定射へ揃える。
方針：元の初点固定 tail の二時刻表示を実際の cone Hom に適用する。
規約：元の全単体と path を保持。使われ方：実反転合成単体の tail との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
variable (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
variable (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)
variable (i j : Fin (n + 1)) (hij : i ≤ j)
include hij

/-- 元の零時刻内の実 cone tail は元の始域の恒等。 -/
lemma pointedMorphismSourceSimplex_tail_zero
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 0)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 0) :
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSourceSimplex_obj_zero f t p i hi)
        (pointedMorphismSourceSimplex_obj_zero f t p j hj)) = toUnit _ ≫ eId SSet K := by
  rw [← simplicialHom_const_id]
  exact morphismInitialTail_map_labels f (stdSimplex.objEquiv t)
    (ULift.up i.succ) (ULift.up j.succ) (Fin.succ_le_succ_iff.mpr hij) 0 0 hi hj (by decide)

/-- 元の一時刻内の実 cone tail は元の終域の恒等。 -/
lemma pointedMorphismSourceSimplex_tail_one
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 1)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSourceSimplex_obj_one f t p i hi)
        (pointedMorphismSourceSimplex_obj_one f t p j hj)) = toUnit _ ≫ eId SSet L := by
  rw [← simplicialHom_const_id]
  exact morphismInitialTail_map_labels f (stdSimplex.objEquiv t)
    (ULift.up i.succ) (ULift.up j.succ) (Fin.succ_le_succ_iff.mpr hij) 1 1 hi hj (by decide)

/-- 元の零から一時刻の実 cone tail は元の指定射。 -/
lemma pointedMorphismSourceSimplex_tail_mixed
    (hi : (stdSimplex.objEquiv t).toOrderHom i = 0)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSourceSimplex_obj_zero f t p i hi)
        (pointedMorphismSourceSimplex_obj_one f t p j hj)) = SSet.const (functorVertex f) := by
  exact morphismInitialTail_map_labels f (stdSimplex.objEquiv t)
    (ULift.up i.succ) (ULift.up j.succ) (Fin.succ_le_succ_iff.mpr hij) 0 1 hi hj (by decide)

end SerrePositivity.InfinityCategories.F2
