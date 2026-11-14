module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.NativeNormalizedHomActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomCoefficientDirectCylinder
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainPostBoundary

/-! 実閉射での元 Hom 正規化は、元の二作用・負 primitive を同じ Yoneda 逆で移した明示 lift。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "q" => CategoryTheory.Iso.inv (dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "h" => -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y

lemma dgGluingNativeNormalizedCochain_boundary :
    δ (-1) 0 (Cochain.comp h (Cochain.ofHom q) (add_zero (-1))) =
      Cochain.ofHom (g ≫ q - f ≫ q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomNegativePrimitive_boundary R C D M X Y) q

def dgGluingNativeNormalizedCochainLift :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R RM (representable R X.left) (M.rightAt Y.right)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
    (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
    (dgGluingNativeNormalizedCochain_boundary R C D M X Y)

lemma dgGluingNativeNormalizedHom_eq_cochainLift :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom R C D M X Y =
      dgGluingNativeNormalizedCochainLift R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R RM RM (DGFunctor.id RM)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (representable R X.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (M.rightAt Y.right)) _
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom_source R C D M X Y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_end R RM (representable R X.left) (M.rightAt Y.right)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
        (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
        (dgGluingNativeNormalizedCochain_boundary R C D M X Y)).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom_replacement R C D M X Y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start R RM (representable R X.left) (M.rightAt Y.right)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) (f ≫ q) (g ≫ q)
        (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
        (dgGluingNativeNormalizedCochain_boundary R C D M X Y)).symm
  · change (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom R C D M X Y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R RM RM (DGFunctor.id RM)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (representable R X.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (M.rightAt Y.right))) (zero_add (-1)) =
      (Cochain.ofHom (dgGluingNativeNormalizedCochainLift R C D M X Y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R RM RM (DGFunctor.id RM)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (representable R X.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (M.rightAt Y.right))) (zero_add (-1))
    rw [dgGluingNativeNormalizedCochainLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_primitive,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom_primitive R C D M X Y, Cochain.neg_comp, neg_neg]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
