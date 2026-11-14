module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeModuleNormalizedPrism

/-! 元実正規化 Hom の全 pinched prism を同じ Yoneda 同型で元負 primitive の係数複体族へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "f" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "h" => -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleCochainCoefficientMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R C) (representable R X.left) (M.rightAt Y.right) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (M.value X.left Y.right) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := RightModule R C)
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max (u + 1) v} (M.value X.left Y.right))
    (x := _root_.SerrePositivity.DifferentialGraded.representable R X.left) (y := M.rightAt Y.right)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
    ((_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).hom)

lemma dgGluingNativeModuleNormalizedPrism_coefficient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (dgGluingNativeModuleCochainCoefficientMap R C D M X Y) =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainModelInput R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y)) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainPrism R C D M X Y) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingNativeModuleCochainCoefficientMap R C D M X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y)) := by
    refine Eq.trans ?_ (congrArg
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainPrism_yoneda R C D M X Y))
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedPrism_cochain, Category.assoc, hp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
