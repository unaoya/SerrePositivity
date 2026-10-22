module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceComparisonEquivalence

/-!
概要：元の指定頂点の slice を、元の関手の像の点の局所 Kan 添字へ比較する。
方針：同じ slice 比較と引き戻しの因子交換を合成し、元の恒等錐を追跡する。
規約：元の関手に inner 性を仮定しない。恒等頂点を厳密に保つ。
使われ方：指定 Kan 単位の成分の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)
local notation "t" => sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))

instance pointLeftKanProjection_rightFibration [Quasicategory D] :
    RightFibration (leftKanProjection f (f.app (Opposite.op ⦋0⦌) y)) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p := t))⟩

instance pointLeftKanShape_quasicategory [Quasicategory C] [Quasicategory D] :
    Quasicategory (leftKanShape f (f.app (Opposite.op ⦋0⦌) y)) :=
  quasicategory_of_innerFibration (leftKanProjection f (f.app (Opposite.op ⦋0⦌) y))

/-- 元の slice から、同じ像の点の元の局所 Kan 添字への比較。 -/
def pointSliceKanComparison : sliceOver (SSet.yonedaEquiv.symm y) ⟶
    leftKanShape f (f.app (Opposite.op ⦋0⦌) y) :=
  pointSliceComparison f y ≫ (pullbackSymmetry t f).hom

lemma pointSliceKanComparison_projection :
    pointSliceKanComparison f y ≫ leftKanProjection f (f.app (Opposite.op ⦋0⦌) y) =
      sliceOverProjection (SSet.yonedaEquiv.symm y) := by
  rw [pointSliceKanComparison, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pointSliceComparison_projection f y

lemma pointSliceKanComparison_slice :
    pointSliceKanComparison f y ≫ pullback.snd f t = pointSlicePostcomp f y := by
  rw [pointSliceKanComparison, Category.assoc, pullbackSymmetry_hom_comp_snd,
    pointSliceComparison, pullback.lift_fst]

/-- 同じ比較は、元の恒等錐を像の点の元の局所恒等頂点へ写す。 -/
lemma pointSliceKanComparison_identity :
    (pointSliceKanComparison f y).app (Opposite.op ⦋0⦌) (sliceIdentityCone y) =
      F1B.kanLeftKanIdentityVertex f y := by
  apply SSet.yonedaEquiv.symm.injective
  have hy : SSet.yonedaEquiv.symm (sliceIdentityCone y) ≫ pointSliceKanComparison f y =
      SSet.yonedaEquiv.symm ((pointSliceKanComparison f y).app (Opposite.op ⦋0⦌)
        (sliceIdentityCone y)) := SSet.yonedaEquiv_symm_comp _ _
  rw [← hy, F1B.kanLeftKanIdentityVertex, Equiv.symm_apply_apply]
  apply pullback.hom_ext
  · rw [Category.assoc, pointSliceKanComparison_projection, pullback.lift_fst]
    simpa only [SSet.yonedaEquiv_symm_comp, sliceIdentityCone_projection]
  · rw [Category.assoc, pointSliceKanComparison_slice, pullback.lift_snd]
    simpa only [SSet.yonedaEquiv_symm_comp, pointSlicePostcomp_identity]

/-- 充満忠実な元の関手では、同じ局所 Kan 比較自体が同値。 -/
lemma pointSliceKanComparison_isQCatEquivalence [Quasicategory C] [Quasicategory D]
    (hf : IsFullyFaithful f) : IsQCatEquivalence (pointSliceKanComparison f y) :=
  (pointSliceComparison_isQCatEquivalence f hf y).comp
    (qCatEquivalenceOfIso (pullbackSymmetry t f)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
