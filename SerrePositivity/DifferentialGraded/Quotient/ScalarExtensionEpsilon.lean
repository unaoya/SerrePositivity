module
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionPaths
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCochain
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonTensor

/-! # 係数変更と次数 +1 の ε 消去 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 生成元 ε↦1 の次数 +1 cochain は係数変更と可換する。 -/
lemma eraseEpsilon_baseChange :
    CochainSquare φ (sphereIso φ (-1)).hom (unitIso φ).hom (eraseEpsilon A) (eraseEpsilon A') := by
  let := φ.toAlgebra
  intro i j hij
  by_cases hi : i = -1
  · subst i
    have hj : j = 0 := by omega
    cases hj
    apply (cancel_epi ((ModuleCat.extendScalars φ).map
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv)).1
    apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (unitIso φ).hom.f 0
      ((ModuleCat.extendScalars φ).map ((eraseEpsilon A).v (-1) 0 (by omega))
        ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (eraseEpsilon A').v (-1) 0 (by omega)
        ((sphereIso φ (-1)).hom.f (-1)
          ((1 : A') ⊗ₜ[A] (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A)))
    have hm := ModuleCat.ExtendScalars.map_tmul φ
      ((eraseEpsilon A).v (-1) 0 (by omega)) (1 : A')
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat A))).inv (1 : A))
    erw [hm]
    erw [eraseEpsilon_generator A]
    erw [sphereIso_one φ (-1)]
  · have hz := (ModuleCat.extendScalars φ).map_isZero
      (isZero_single_obj_X (.up ℤ) (-1) (𝟙_ (ModuleCat A)) i hi)
    exact hz.eq_of_src _ _

end SerrePositivity.DifferentialGraded.DGQuotient
