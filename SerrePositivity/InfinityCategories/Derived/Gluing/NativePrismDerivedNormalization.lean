module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePrismNormalizedFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedAugmentationIntervalNormalization

/-! 元 prism の実正規化族を主比較の導来区間 Hom へ移し、同じ全明示族との厳密比較を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeDerivedNormalizedPrism (X Y : DGGluingObject R C D M) :=
  dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
      (dgGluingNativePrismNormalizedFamily R C D M X Y) ≫
    dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
      (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
        pinchedHomToIntervalMappingSpace _ _

lemma dgGluingNativeDerivedNormalizedPrism_comparison (X Y : DGGluingObject R C D M) :
    dgGluingNativeDerivedNormalizedPrism R C D M X Y =
      ((Δ[1] : SSet.{max (u + 1) v w}) ◁
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map (pinchedComplexModelIso X Y).hom) ≫
        dgGluingHomDerivedAugmentationIntervalPrism R C D M X Y := by
  have hn := congrArg (dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1)
    (dgGluingNativePrismNormalizedFamily_comparison R C D M X Y)
  have hu := dgGluingUliftSimplexFamily_precomp.{max u v w, max (u + 1) v w}
    (dgGluingHomCoefficientAugmentationPrism R C D M X Y) (pinchedComplexModelIso X Y).hom
  have hs := hn.trans hu.symm
  dsimp only [dgGluingNativeDerivedNormalizedPrism, dgGluingHomDerivedAugmentationIntervalPrism,
    dgGluingHomDerivedAugmentationPrism]
  rw [hs]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories
