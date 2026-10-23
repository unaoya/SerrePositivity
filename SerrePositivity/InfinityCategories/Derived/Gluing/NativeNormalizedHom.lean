module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityComma
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizeHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison

/-! 実標準閉射で正規化した元 gluing Hom は、元比較 primitive の同じ全 Yoneda 像を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "E" => RightModule R C
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeNormalizedHom :=
  (dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
    dgGluingIdentityCommaNormalizeHom R E IX IY

lemma dgGluingNativeNormalizedHom_primitive :
    (Cochain.ofHom (dgGluingNativeNormalizedHom R C D M X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (representable R X.left))
        (dgGluingIdentityCommaObject R E (M.rightAt Y.right))) (zero_add (-1)) =
      (dgGluingHomPrimitive R C D M X Y).comp
        (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv) (add_zero (-1)) := by
  change (Cochain.ofHom ((dgGluingNativeIdentityCommaFunctor R C D M).map X Y ≫
    dgGluingIdentityCommaNormalizeHom R E IX IY)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E
          (dgGluingNativeIdentityCommaObject R C D M X).replacement)
        (dgGluingIdentityCommaObject R E
          (dgGluingNativeIdentityCommaObject R C D M Y).source)) (zero_add (-1)) = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingIdentityCommaNormalizeHom_primitive R E IX IY,
    dgGluingNativeIdentityCommaFunctor_map, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  have hi := dgGluingCommaImageHomMap_primitive R D E M.toFunctor
    (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)
  have hh := congrArg (fun p : Cochain
      (dgFunctorCommaHomComplex R D E M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y))
      (homObject R E (representable R X.left) (M.rightAt Y.right)) (-1) =>
        (Cochain.ofHom ((dgGluingToComma R C D M).map X Y)).comp p (zero_add (-1))) hi
  exact hh.trans (dgGluingHomRepresentableIso_primitive R C D M X Y)

end SerrePositivity.InfinityCategories
