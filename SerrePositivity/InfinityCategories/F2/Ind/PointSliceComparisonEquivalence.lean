module

public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceComparisonFiber

/-!
概要：任意の充満忠実な元の関手の slice 比較自体が同値。
方針：元の Hom 作用の同値を各 fiber に移し、right fibration の比較判定を使う。
規約：関手の inner fibration 性を要求しない。
使われ方：像の点の局所 Kan 添字の恒等頂点を終対象として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
  (f : C ⟶ D) (hf : IsFullyFaithful f) (y : C _⦋0⦌)
include hf

/-- 元の充満忠実な関手の同じ slice 比較は、全指定 fiber 上で同値。 -/
lemma pointSliceComparison_fiber_isQCatEquivalence (x : C _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap (sliceOverProjection (SSet.yonedaEquiv.symm y))
      (pointSlicePullbackProjection f y) (pointSliceComparison f y)
        (pointSliceComparison_projection f y) x) := by
  have ht := (qCatEquivalenceOfIso (pinchedHomSliceFiberIso
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y))).isQCatEquivalence
  have h := (hf x y).isQCatEquivalence.comp ht
  have h' := (congrArg (fun g => IsQCatEquivalence g) (pointSliceComparison_fiber_hom f x y)).mpr h
  have h₀ := (qCatEquivalenceOfIso (pinchedHomSliceFiberIso x y)).isQCatEquivalence
  have h₁ := (qCatEquivalenceOfIso (vertexFiberPullbackIso
    (sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) y))) f x)).isQCatEquivalence
  exact h₁.cancel_right (h₀.cancel_left h')

/-- 任意の充満忠実な元の関手の同じ slice 比較自体が同値。 -/
lemma pointSliceComparison_isQCatEquivalence : IsQCatEquivalence (pointSliceComparison f y) :=
  isQCatEquivalence_of_rightFibration_fibers (sliceOverProjection (SSet.yonedaEquiv.symm y))
    (pointSlicePullbackProjection f y) (pointSliceComparison f y) (pointSliceComparison_projection f y)
    (pointSliceComparison_fiber_isQCatEquivalence f hf y)

end SerrePositivity.InfinityCategories.F2.Ind
