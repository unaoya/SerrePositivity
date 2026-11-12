module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedAugmentationNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCoefficientIntervalPrism

/-! 明示 augmentation を主比較の区間 Hom へ移し、同じ係数対角の全区間族と両端固定で比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedAugmentationIntervalPrism (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

lemma dgGluingHomDerivedAugmentationIntervalNormalization_exists
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingHomDerivedAugmentationIntervalPrism R C D M X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y),
      (((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))) ▷
          (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v w}) ⊗
            (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))) ≫
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationNormalization_exists R C D M X Y
  let q := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _
  have he : uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCoefficientIntervalPrism_eq R C D M X Y).symm
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q
  let U := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T rfl he
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc, he]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
