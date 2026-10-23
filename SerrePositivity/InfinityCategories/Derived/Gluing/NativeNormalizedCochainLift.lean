module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizedHomActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientDirectCylinder
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPostBoundary

/-! 実閉射での元 Hom 正規化は、元の二作用・負 primitive を同じ Yoneda 逆で移した明示 lift。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y
local notation "g" => dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y
local notation "h" => -dgGluingHomPrimitive R C D M X Y

lemma dgGluingNativeNormalizedCochain_boundary :
    δ (-1) 0 (Cochain.comp h (Cochain.ofHom q) (add_zero (-1))) =
      Cochain.ofHom (g ≫ q - f ≫ q) :=
  dgGluingCochainPost_boundary f g h (dgGluingHomNegativePrimitive_boundary R C D M X Y) q

def dgGluingNativeNormalizedCochainLift :=
  dgGluingCochainIdentityCommaLift R RM (representable R X.left) (M.rightAt Y.right)
    (dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
    (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
    (dgGluingNativeNormalizedCochain_boundary R C D M X Y)

lemma dgGluingNativeNormalizedHom_eq_cochainLift :
    dgGluingNativeNormalizedHom R C D M X Y =
      dgGluingNativeNormalizedCochainLift R C D M X Y := by
  apply dgFunctorCommaHom_ext R RM RM (DGFunctor.id RM)
    (dgGluingIdentityCommaObject R RM (representable R X.left))
    (dgGluingIdentityCommaObject R RM (M.rightAt Y.right)) _
  · exact (dgGluingNativeNormalizedHom_source R C D M X Y).trans
      (dgGluingCochainIdentityCommaLift_end R RM (representable R X.left) (M.rightAt Y.right)
        (dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
        (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
        (dgGluingNativeNormalizedCochain_boundary R C D M X Y)).symm
  · exact (dgGluingNativeNormalizedHom_replacement R C D M X Y).trans
      (dgGluingCochainIdentityCommaLift_start R RM (representable R X.left) (M.rightAt Y.right)
        (dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
        (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
        (dgGluingNativeNormalizedCochain_boundary R C D M X Y)).symm
  · change (Cochain.ofHom (dgGluingNativeNormalizedHom R C D M X Y)).comp
        (dgFunctorCommaPrimitive R RM RM (DGFunctor.id RM)
          (dgGluingIdentityCommaObject R RM (representable R X.left))
          (dgGluingIdentityCommaObject R RM (M.rightAt Y.right))) (zero_add (-1)) =
      (Cochain.ofHom (dgGluingNativeNormalizedCochainLift R C D M X Y)).comp
        (dgFunctorCommaPrimitive R RM RM (DGFunctor.id RM)
          (dgGluingIdentityCommaObject R RM (representable R X.left))
          (dgGluingIdentityCommaObject R RM (M.rightAt Y.right))) (zero_add (-1))
    rw [dgGluingNativeNormalizedCochainLift, dgGluingCochainIdentityCommaLift_primitive,
      dgGluingNativeNormalizedHom_primitive R C D M X Y, Cochain.neg_comp, neg_neg]

end SerrePositivity.InfinityCategories
