module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativePrismNormalizedSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SimplicialMapOfPointwise

/-! 元 gluing prism の実正規化係数から全単体的区間族を構成し、同じ明示 cochain prism と照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

def dgGluingNativePrismNormalizedFamily (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (Δ[1] : SSet.{max u v w}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (M.value X.left Y.right) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplicialMapOfPointwise
    (((Δ[1] : SSet.{max u v w}) ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y)
    (fun _ z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedSimplex R C D M z.2 z.1)
    (by rintro ⟨⟨n⟩⟩ z; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePrismNormalizedSimplex_eq R C D M z.2 z.1)

lemma dgGluingNativePrismNormalizedFamily_comparison (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingNativePrismNormalizedFamily R C D M X Y =
      ((Δ[1] : SSet.{max u v w}) ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplicialMapOfPointwise_eq _ _ _

lemma dgGluingNativePrismNormalizedFamily_zero (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingNativePrismNormalizedFamily R C D M X Y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) := by
  rw [dgGluingNativePrismNormalizedFamily_comparison, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun p => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism_zero R C D M X Y)

lemma dgGluingNativePrismNormalizedFamily_one (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingNativePrismNormalizedFamily R C D M X Y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) := by
  rw [dgGluingNativePrismNormalizedFamily_comparison, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  exact congrArg (fun p => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y).hom ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism_one R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
