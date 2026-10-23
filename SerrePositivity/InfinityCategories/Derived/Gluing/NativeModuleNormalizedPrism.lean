module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeModuleCochainInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSimplexFamilies

/-! 実 native 正規化 Hom に元 augmentation を適用した全 pinched prism は、同じ明示 cochain 族。 -/
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
local notation "RM" => RightModule R C
local notation "K" => dgGluingHomComplex R C D M X Y
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleNormalizedPrism :=
  (Δ[1] ◁ dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    (C := DGGluingObject R C D M) (D := Q) (x := X) (y := Y)
    (x' := dgGluingIdentityCommaObject R RM (representable R X.left))
    (y' := dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
    (dgGluingNativeNormalizedHom R C D M X Y)) ≫
      dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (dgGluingIdentityCommaPinchedPrism R RM (representable R X.left) (M.rightAt Y.right))

lemma dgGluingNativeModuleNormalizedPrism_cochain :
    (Δ[1] ◁ dgGluingNativeModuleCochainModelInput R C D M X Y) ≫
        dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
          (dgGluingNativeModuleCochainPrism R C D M X Y) =
      dgGluingNativeModuleNormalizedPrism R C D M X Y := by
  have hu := dgGluingUliftSimplexFamily_precomp.{max (u + 1) v, max (u + 1) v w}
    (dgGluingIdentityCommaPinchedPrism R RM (representable R X.left) (M.rightAt Y.right))
    (dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
      R RM (representable R X.left) (M.rightAt Y.right)
      K (f ≫ q) (g ≫ q) (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
      (dgGluingNativeNormalizedCochain_boundary R C D M X Y))
  change _ = dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
    (dgGluingNativeModuleCochainPrism R C D M X Y) at hu
  rw [← hu, ← Category.assoc, ← whiskerLeft_comp, dgGluingNativeModuleCochainInput_factor]
  rw [dgGluingNativeModuleNormalizedPrism, dgGluingNativeNormalizedHom_eq_cochainLift]

end SerrePositivity.InfinityCategories
