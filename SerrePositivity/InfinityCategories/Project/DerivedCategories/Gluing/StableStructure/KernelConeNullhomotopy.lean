module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeKernelRightArrow

/-! 標準 kernel 円錐への合成を、元の Hom 円錐の次数 −1 包含で零ホモトピーにする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f
local notation "kf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M)) f

omit [Small.{u} D] in
/-- native の閉単位への後合成は、元の同じ閉射を回収する。 -/
lemma dgGluingIdentity_postcomposition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity R C D M Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M Y Y Z f =
      ForgetEnrichment.homTo (Complex R) f := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosed_postcompose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (𝟙 (ForgetEnrichment.of (Complex R) Y)) f
  simpa only [Category.id_comp, eHomEquiv_id] using! he

/-- 標準 Hom 円錐の左包含を、同じ kernel Hom 同型で送った次数 −1 の cochain。 -/
def dgGluingKernelConeNullCochain :
    Cochain (𝟙_ (Complex R))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F KY L) (-1) :=
  (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity R C D M Y)).comp
    ((mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M Y Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M Y Y Z f).hom)
      (add_zero (-1))) (zero_add (-1))

/-- この同じ cochain の境界は、元の kernel 閉射と標準円錐包含の合成。 -/
lemma dgGluingKernelConeNullCochain_boundary :
    δ (-1) 0 (dgGluingKernelConeNullCochain R C D M Y Z f) =
      Cochain.ofHom (ForgetEnrichment.homTo (Complex R) (kf ≫ i)) := by
  rw [dgGluingKernelConeNullCochain, δ_ofHom_comp, δ_comp_ofHom, mappingCone.δ_inl,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso_inr, ← Category.assoc,
    dgGluingIdentity_postcomposition]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosed_postcompose R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C) (Morita.kernelTensor R D C M))
    kf i
  change ForgetEnrichment.homTo (Complex R) kf ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) KY) i =
      ForgetEnrichment.homTo (Complex R) (kf ≫ i) at he
  change (ForgetEnrichment.homTo (Complex R) f ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).map Y Z) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConePost R C D M Y Y Z f = _ at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, Category.assoc] at he
  exact congrArg Cochain.ofHom he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
