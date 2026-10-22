module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelRightArrow

/-! 標準 kernel 円錐への合成を、元の Hom 円錐の次数 −1 包含で零ホモトピーにする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "i" => dgGluingKernelConeInr R C D M Y Z f
local notation "kf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgGluingToKernelComma R C D M)) f

omit [Small.{u} D] in
/-- native の閉単位への後合成は、元の同じ閉射を回収する。 -/
lemma dgGluingIdentity_postcomposition :
    dgGluingIdentity R C D M Y ≫ dgGluingPostcomposition R C D M Y Y Z f =
      ForgetEnrichment.homTo (Complex R) f := by
  have he := dgGluingClosed_postcompose R (DGGluingObject R C D M)
    (𝟙 (ForgetEnrichment.of (Complex R) Y)) f
  simpa only [Category.id_comp, eHomEquiv_id] using! he

/-- 標準 Hom 円錐の左包含を、同じ kernel Hom 同型で送った次数 −1 の cochain。 -/
def dgGluingKernelConeNullCochain :
    Cochain (𝟙_ (Complex R))
      (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F KY L) (-1) :=
  (Cochain.ofHom (dgGluingIdentity R C D M Y)).comp
    ((mappingCone.inl (dgGluingPostcomposition R C D M Y Y Z f)).comp
      (Cochain.ofHom (dgGluingHomConeKernelIso R C D M Y Y Z f).hom)
      (add_zero (-1))) (zero_add (-1))

/-- この同じ cochain の境界は、元の kernel 閉射と標準円錐包含の合成。 -/
lemma dgGluingKernelConeNullCochain_boundary :
    δ (-1) 0 (dgGluingKernelConeNullCochain R C D M Y Z f) =
      Cochain.ofHom (ForgetEnrichment.homTo (Complex R) (kf ≫ i)) := by
  rw [dgGluingKernelConeNullCochain, δ_ofHom_comp, δ_comp_ofHom, mappingCone.δ_inl,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [Category.assoc, dgGluingHomConeKernelIso_inr, ← Category.assoc,
    dgGluingIdentity_postcomposition]
  have he := dgGluingClosed_postcompose R
    (DGFunctorCommaObject R (RightModule R D) (RightModule R C) (Morita.kernelTensor R D C M))
    kf i
  change ForgetEnrichment.homTo (Complex R) kf ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) KY) i =
      ForgetEnrichment.homTo (Complex R) (kf ≫ i) at he
  change (ForgetEnrichment.homTo (Complex R) f ≫
    (dgGluingToKernelComma R C D M).map Y Z) ≫
      dgGluingKernelConePost R C D M Y Y Z f = _ at he
  rw [dgGluingToKernelComma_map, Category.assoc] at he
  exact congrArg Cochain.ofHom he

end SerrePositivity.InfinityCategories
