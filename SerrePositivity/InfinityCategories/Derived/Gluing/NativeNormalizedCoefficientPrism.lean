module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeModuleNormalizedPrism

/-! 元実正規化 Hom の全 pinched prism を同じ Yoneda 同型で元負 primitive の係数複体族へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleCochainCoefficientMap :
    DGNerve.pinchedHom R (RightModule R C) (representable R X.left) (M.rightAt Y.right) ⟶
      complexPinchedSpace.{u, max (u + 1) v} (M.value X.left Y.right) :=
  pinchedHomChainMap (D := RightModule R C)
    (E := DGComplexPinchedModel.{u, max (u + 1) v} (M.value X.left Y.right))
    (x := representable R X.left) (y := M.rightAt Y.right)
    (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
    ((dgYonedaIso R X.left (M.rightAt Y.right)).hom ≫
      (complexUnitHomIso (M.value X.left Y.right)).hom)

lemma dgGluingNativeModuleNormalizedPrism_coefficient :
    dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (dgGluingNativeModuleCochainCoefficientMap R C D M X Y) =
      (Δ[1] ◁ dgGluingNativeModuleCochainModelInput R C D M X Y) ≫
        dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
          (dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
            (dgGluingHomNegativePrimitive_boundary R C D M X Y)) := by
  have hp : dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
      (dgGluingNativeModuleCochainPrism R C D M X Y) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingNativeModuleCochainCoefficientMap R C D M X Y) =
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (dgGluingComplexCochainAugmentationPrism.{u, max (u + 1) v} f g h
          (dgGluingHomNegativePrimitive_boundary R C D M X Y)) := by
    refine Eq.trans ?_ (congrArg
      (dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1)
      (dgGluingNativeModuleCochainPrism_yoneda R C D M X Y))
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← dgGluingNativeModuleNormalizedPrism_cochain, Category.assoc, hp]

end SerrePositivity.InfinityCategories
