module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeIdentityComma
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaNormalizeHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrimitiveComparison

/-! 実標準閉射で正規化した元 gluing Hom は、元比較 primitive の同じ全 Yoneda 像を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "E" => RightModule R C
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeNormalizedHom :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E IX IY

lemma dgGluingNativeNormalizedHom_primitive :
    (Cochain.ofHom (dgGluingNativeNormalizedHom R C D M X Y)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (M.rightAt Y.right))) (zero_add (-1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).comp
        (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv) (add_zero (-1)) := by
  change (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E IX IY)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X).replacement)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y).source)) (zero_add (-1)) = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom_primitive R E IX IY,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor_map, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_primitive R D E M.toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)
  have hh := congrArg (fun p : Cochain
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R D E M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y))
      (homObject R E (representable R X.left) (M.rightAt Y.right)) (-1) =>
        (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).map X Y)).comp p (zero_add (-1))) hi
  exact hh.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
