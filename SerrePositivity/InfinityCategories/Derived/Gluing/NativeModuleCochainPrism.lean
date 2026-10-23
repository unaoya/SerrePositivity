module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationIsoTarget

/-! 元 Hom の負 primitive の加群値明示 prism は、同じ Yoneda 同型で係数複体の全明示族へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleCochainPrism :=
  dgGluingCochainAugmentationPrism.{u, max (u + 1) v}
    R RM (representable R X.left) (M.rightAt Y.right)
    (dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
    (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
    (dgGluingNativeNormalizedCochain_boundary R C D M X Y)

lemma dgGluingNativeModuleCochainPrism_yoneda :
    dgGluingNativeModuleCochainPrism R C D M X Y ≫
      pinchedHomChainMap (D := RightModule R C)
        (E := DGComplexPinchedModel.{u, max (u + 1) v} (M.value X.left Y.right))
        (x := representable R X.left) (y := M.rightAt Y.right)
        (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
        ((dgYonedaIso R X.left (M.rightAt Y.right)).hom ≫
          (complexUnitHomIso (M.value X.left Y.right)).hom) =
      dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
        (dgGluingHomNegativePrimitive_boundary R C D M X Y) :=
  dgGluingCochainAugmentationPrism_iso_target.{u, max (u + 1) v}
    R RM (representable R X.left) (M.rightAt Y.right)
    (dgYonedaIso R X.left (M.rightAt Y.right)) f g h
    (dgGluingHomNegativePrimitive_boundary R C D M X Y)

end SerrePositivity.InfinityCategories
