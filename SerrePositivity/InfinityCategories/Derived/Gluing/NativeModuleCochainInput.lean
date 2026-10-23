module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeModuleCochainPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationHomInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedInputChainMap

/-! 元一般宇宙の Hom から、同じ単位 Hom 模型を介した明示 cochain 入力を厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "K" => dgGluingHomComplex R C D M X Y
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleCochainModelInput :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (complexPinchedSpace.{u, max (u + 1) v} K) :=
  dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    (C := DGGluingObject R C D M) (D := DGComplexPinchedModel.{u, max (u + 1) v} K)
    (x := X) (y := Y) (x' := complexPinchedSource K) (y' := complexPinchedTarget K)
    (complexUnitHomIso K).hom

lemma dgGluingNativeModuleCochainInput_chainMap :
    dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
        R RM (representable R X.left) (M.rightAt Y.right)
        K (f ≫ q) (g ≫ q) (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
        (dgGluingNativeNormalizedCochain_boundary R C D M X Y) =
      pinchedHomChainMap (D := DGComplexPinchedModel.{u, max (u + 1) v} K) (E := Q)
        (x := complexPinchedSource K) (y := complexPinchedTarget K)
        (x' := dgGluingIdentityCommaObject R RM (representable R X.left))
        (y' := dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
        ((complexUnitHomIso K).inv ≫ dgGluingNativeNormalizedCochainLift R C D M X Y) :=
  dgGluingComplexPinchedInput_eq_chainMap
    (E := Q) (x := dgGluingIdentityCommaObject R RM (representable R X.left))
    (y := dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
    (dgGluingNativeNormalizedCochainLift R C D M X Y)

lemma dgGluingNativeModuleCochainInput_factor :
    dgGluingNativeModuleCochainModelInput R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
            R RM (representable R X.left) (M.rightAt Y.right)
            K (f ≫ q) (g ≫ q) (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
            (dgGluingNativeNormalizedCochain_boundary R C D M X Y)) =
      dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
        (C := DGGluingObject R C D M) (D := Q) (x := X) (y := Y)
        (x' := dgGluingIdentityCommaObject R RM (representable R X.left))
        (y' := dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
        (dgGluingNativeNormalizedCochainLift R C D M X Y) := by
  rw [dgGluingNativeModuleCochainInput_chainMap]
  have ht := dgGluingUniverseHomChainMap_post.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    (C := DGGluingObject R C D M) (D := DGComplexPinchedModel.{u, max (u + 1) v} K) (E := Q)
    (x := X) (y := Y) (x' := complexPinchedSource K) (y' := complexPinchedTarget K)
    (x'' := dgGluingIdentityCommaObject R RM (representable R X.left))
    (y'' := dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
    (complexUnitHomIso K).hom
    ((complexUnitHomIso K).inv ≫ dgGluingNativeNormalizedCochainLift R C D M X Y)
  simpa only [dgGluingNativeModuleCochainModelInput, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp] using ht

end SerrePositivity.InfinityCategories
