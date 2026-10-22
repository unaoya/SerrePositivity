module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePrismNormalizedFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopyPrecomp
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationNormalization

/-! 元 prism の実係数から作る正規化族と主係数 path を、元 pinched Hom 全体で両端固定比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeCoefficientPathPrism (X Y : DGGluingObject R C D M) :=
  ((Δ[1] : SSet.{max u v w}) ◁ (pinchedComplexModelIso X Y).hom) ≫
    uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y)

lemma dgGluingNativePrismNormalizedPathComparison_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingNativePrismNormalizedFamily R C D M X Y)
        (dgGluingNativeCoefficientPathPrism R C D M X Y),
      (((SSet.boundary 1).ι ▷ DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) ▷
          (Δ[1] : SSet.{max u v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v w}) ⊗
            DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) ≫
            dgGluingNativeCoefficientPathPrism R C D M X Y := by
  obtain ⟨H, hH⟩ := dgGluingHomCoefficientAugmentationNormalization_exists R C D M X Y
  let T := functorHomotopyPrecomp H ((Δ[1] : SSet.{max u v w}) ◁ (pinchedComplexModelIso X Y).hom)
  let U := stableHomotopyRetarget T
    (dgGluingNativePrismNormalizedFamily_comparison R C D M X Y).symm rfl
  refine ⟨U, ?_⟩
  rw [dgGluingHomotopyRetarget_h]
  exact dgGluingRelativePrismHomotopy_precomp_boundary H (pinchedComplexModelIso X Y).hom hH

end SerrePositivity.InfinityCategories
