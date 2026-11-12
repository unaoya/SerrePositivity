module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainAugmentationIsoTarget

/-! 元 Hom の負 primitive の加群値明示 prism は、同じ Yoneda 同型で係数複体の全明示族へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "h" => -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleCochainPrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism.{u, max (u + 1) v}
    R RM (representable R X.left) (M.rightAt Y.right)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
    (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedCochain_boundary R C D M X Y)

lemma dgGluingNativeModuleCochainPrism_yoneda :
    dgGluingNativeModuleCochainPrism R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := RightModule R C)
        (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max (u + 1) v} (M.value X.left Y.right))
        (x := representable R X.left) (y := M.rightAt Y.right)
        (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
        ((dgYonedaIso R X.left (M.rightAt Y.right)).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (M.value X.left Y.right)).hom) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_iso_target.{u, max (u + 1) v}
    R RM (representable R X.left) (M.rightAt Y.right)
    (dgYonedaIso R X.left (M.rightAt Y.right)) f g h
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
