module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeUnit

/-!
概要：KST Def3.1 の Koszul cochain 底変更同型は乗法を保つ。
方針：係数変更した同次 tensor の1⊗(x⊗y)で比較し、逆外積代数射の積保存を使う。
規約：既存の強モノイダルな係数変更の tensorIso を使う。
使われ方：底変更 dg 関手の map_comp。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：逆 Koszul cochain 底変更同型は係数変更した乗法を保つ。
方針：tensorIso の順写像を前合成し、底変更 tensor の同次生成元で代数射の map_mul を使う。
規約：KST Def3.1。使われ方：底変更 dg 関手の map_comp。 -/
theorem exteriorCochainBaseChange_mul (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    (DifferentialGraded.ScalarExtension.tensorIso φ (exteriorKoszulCochain d)
        (exteriorKoszulCochain d)).inv ≫
      (DifferentialGraded.ScalarExtension.extension φ).map (exteriorKoszulMultiplication d) ≫
        (exteriorCochainBaseChangeIso φ d).inv =
      ((exteriorCochainBaseChangeIso φ d).inv ⊗ₘ (exteriorCochainBaseChangeIso φ d).inv) ≫
        exteriorKoszulMultiplication (exteriorBaseChangeDifferential (S := S) d) := by
  let := φ.toAlgebra
  apply (cancel_epi (DifferentialGraded.ScalarExtension.tensorIso φ
    (exteriorKoszulCochain d) (exteriorKoszulCochain d)).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorBaseChange_hom_ext φ (exteriorKoszulCochain d) (exteriorKoszulCochain d)
  intro p q hpq
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (exteriorCochainBaseChangeIso φ d).inv.f n
      ((ModuleCat.extendScalars φ).map ((exteriorKoszulMultiplication d).f n)
        ((1 : S) ⊗ₜ[R] ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
          p q n hpq (x ⊗ₜ[R] y))) =
    (exteriorKoszulMultiplication (exteriorBaseChangeDifferential (S := S) d)).f n
      (((exteriorCochainBaseChangeIso φ d).inv ⊗ₘ
          (exteriorCochainBaseChangeIso φ d).inv).f n
        ((DifferentialGraded.ScalarExtension.tensorIso φ (exteriorKoszulCochain d)
          (exteriorKoszulCochain d)).hom.f n
          ((1 : S) ⊗ₜ[R] ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
            p q n hpq (x ⊗ₜ[R] y))))
  erw [ModuleCat.ExtendScalars.map_tmul φ, exteriorKoszulMultiplication_apply,
    cochainTensorBaseChangeIso_apply_ι φ (exteriorKoszulCochain d) (exteriorKoszulCochain d)
      p q n hpq x y]
  erw [cochainTensorMap_apply_ι, exteriorKoszulMultiplication_apply]
  apply exteriorCochainInclusion_injective (exteriorBaseChangeDifferential (S := S) d) n
  rw [exteriorBaseChangeCochainInclusion_iso_inv, exteriorCochainInclusion_product,
    exteriorBaseChangeCochainInclusion_iso_inv, exteriorBaseChangeCochainInclusion_iso_inv]
  change exteriorOfBaseChange ((1 : S) ⊗ₜ[R]
      exteriorCochainInclusion d n (exteriorCochainBilinear d p q n hpq x y)) =
    exteriorOfBaseChange ((1 : S) ⊗ₜ[R] exteriorCochainInclusion d p x) *
      exteriorOfBaseChange ((1 : S) ⊗ₜ[R] exteriorCochainInclusion d q y)
  rw [exteriorCochainInclusion_product, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end SerrePositivity.KST.DerivedBlowup
