module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativePrismDerivedNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopyPrecomp

/-! 元 gluing prism の導来正規化族と、主係数対角の同じ全区間族を両端固定で比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeDerivedCoefficientIntervalPrism (X Y : DGGluingObject R C D M) :=
  ((Δ[1] : SSet.{max (u + 1) v w}) ◁
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map (pinchedComplexModelIso X Y).hom) ≫
    dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y

lemma dgGluingNativeDerivedPrismPathComparison_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingNativeDerivedNormalizedPrism R C D M X Y)
        (dgGluingNativeDerivedCoefficientIntervalPrism R C D M X Y),
      (((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y)) ▷
          (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v w}) ⊗
            (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
              (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y)) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y)) ≫
              dgGluingNativeDerivedCoefficientIntervalPrism R C D M X Y := by
  obtain ⟨H, hH⟩ := dgGluingHomDerivedAugmentationIntervalNormalization_exists R C D M X Y
  let a := (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
    (pinchedComplexModelIso (A := R) X Y).hom
  let T := functorHomotopyPrecomp H ((Δ[1] : SSet.{max (u + 1) v w}) ◁ a)
  let U := stableHomotopyRetarget T
    (dgGluingNativeDerivedNormalizedPrism_comparison R C D M X Y).symm rfl
  refine ⟨U, ?_⟩
  rw [dgGluingHomotopyRetarget_h]
  exact dgGluingRelativePrismHomotopy_precomp_boundary H a hH

end SerrePositivity.InfinityCategories
