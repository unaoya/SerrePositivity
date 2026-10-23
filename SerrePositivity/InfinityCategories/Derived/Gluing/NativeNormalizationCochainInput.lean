module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeModuleCochainInput

/-! 実後合成 cube の正規化入力は、元二作用・負 primitive の明示 cochain 入力そのもの。 -/
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
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

lemma dgGluingNativeNormalizationHomInput_cochain :
    dgGluingNativeNormalizationHomInput R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (pinchedHomChainMap (D := Q) (E := Q)
            (dgGluingIdentityCommaNormalizeHom R RM IX IY)) =
      dgGluingNativeModuleCochainModelInput R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
            R RM (representable R X.left) (M.rightAt Y.right) (dgGluingHomComplex R C D M X Y)
            (f ≫ q) (g ≫ q) (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
            (dgGluingNativeNormalizedCochain_boundary R C D M X Y)) := by
  rw [dgGluingNativeNormalizationHomInput_normalized, dgGluingNativeNormalizedHom_eq_cochainLift,
    dgGluingNativeModuleCochainInput_factor]

end SerrePositivity.InfinityCategories
