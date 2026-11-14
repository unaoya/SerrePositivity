module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativePrismDerivedNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.RelativePrismHomotopyPrecomp

/-! 元 gluing prism の導来正規化族と、主係数対角の同じ全区間族を両端固定で比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeDerivedCoefficientIntervalPrism (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  ((Δ[1] : SSet.{max (u + 1) v w}) ◁
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y

lemma dgGluingNativeDerivedPrismPathComparison_exists (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedNormalizedPrism R C D M X Y)
        (dgGluingNativeDerivedCoefficientIntervalPrism R C D M X Y),
      (((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y)) ▷
          (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v w}) ⊗
            (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
              (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y)) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y)) ≫
              dgGluingNativeDerivedCoefficientIntervalPrism R C D M X Y := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationIntervalNormalization_exists R C D M X Y
  let a := (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) X Y).hom
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H ((Δ[1] : SSet.{max (u + 1) v w}) ◁ a)
  let U := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedNormalizedPrism_comparison R C D M X Y).symm rfl
  refine ⟨U, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativePrismHomotopy_precomp_boundary H a hH

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
