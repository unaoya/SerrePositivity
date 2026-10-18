module

public import SerrePositivity.KST.DerivedBlowup.ExteriorUnitLaws

/-!
概要：KST Def3.1 の Koszul 外積模型の符号付き可換性。
方針：外積の純粋積の反可換性を同次部分加群へ延長し、整数次数の符号に合わせる。
規約：任意可換環上。標数2でも外積による模型を使う。
使われ方：Koszul チャートを可換 dg 代数として扱うための乗法比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory MonoidalCategory HomologicalComplex

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：同次外積の積の符号付き可換性。
方針：各同次部分の span を使い、純粋外積の反可換性へ帰着する。
規約：KST Def3.1、外積次数は自然数。使われ方：cochain の可換性。 -/
theorem exteriorHomogeneous_anticomm (p q : ℕ) (x y : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R p M)
    (hy : y ∈ ExteriorAlgebra.exteriorPower R q M) :
    x * y = ((-1 : ℤˣ) ^ (q * p)) • (y * x) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx hy
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y = ((-1 : ℤˣ) ^ (q * p)) • (y * x))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨mx, rfl⟩ ⟨my, rfl⟩
    exact ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R mx my
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ hx hy
    simp only [add_mul, mul_add, hx, hy, smul_add]
  · intro x y z _ _ _ hy hz
    simp only [mul_add, add_mul, hy, hz, smul_add]
  · intro r x y _ _ hxy
    rw [Algebra.smul_mul_assoc, hxy, Algebra.mul_smul_comm]
    exact smul_comm r ((-1 : ℤˣ) ^ (q * p)) (y * x)
  · intro r x y _ _ hxy
    rw [Algebra.mul_smul_comm, hxy, Algebra.smul_mul_assoc]
    exact smul_comm r ((-1 : ℤˣ) ^ (q * p)) (y * x)

/-- 概要：Koszul cochain 積の整数符号付き可換性。
方針：総外積への単射で同次反可換性を使い、非正次数の符号を比較する。
規約：KST Def3.1、符号は (-1)^(pq)。使われ方：tensor braiding と乗法の適合性。 -/
theorem exteriorCochainBilinear_comm (d : M →ₗ[R] R) (p q n : ℤ) (h : p + q = n)
    (x : (exteriorKoszulCochain d).X p) (y : (exteriorKoszulCochain d).X q) :
    exteriorCochainBilinear d p q n h x y =
      (p * q).negOnePow • exteriorCochainBilinear d q p n (by omega) y x := by
  apply exteriorCochainInclusion_injective d n
  simp only [Units.smul_def, map_zsmul]
  rw [exteriorCochainInclusion_product, exteriorCochainInclusion_product]
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · have hs : (((-q).toNat * (-p).toNat : ℕ) : ℤ) = p * q := by
        rw [Nat.cast_mul, Int.toNat_of_nonneg (by omega : 0 ≤ -q),
          Int.toNat_of_nonneg (by omega : 0 ≤ -p)]
        ring
      have hc := exteriorHomogeneous_anticomm (-p).toNat (-q).toNat
        (exteriorCochainInclusion d p x) (exteriorCochainInclusion d q y)
        (exteriorCochainInclusion_mem d p x) (exteriorCochainInclusion_mem d q y)
      rw [← zpow_natCast, hs, ← Int.negOnePow_def] at hc
      exact hc
    · have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq))
      have hy : y = 0 := Subsingleton.elim _ _
      simp [hy]
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d p (lt_of_not_ge hp))
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]

/-- 概要：Koszul 乗法は Ch(R) の符号付き braiding に関して可換。
方針：純粋同次 tensor で braiding を評価し、cochain 積の可換性を使う。
規約：KST Def3.1。使われ方：Koszul cdga の可換乗法。 -/
theorem exteriorKoszul_comm (d : M →ₗ[R] R) :
    (DifferentialGraded.signedSwap (exteriorKoszulCochain d)
      (exteriorKoszulCochain d)).hom ≫ exteriorKoszulMultiplication d =
      exteriorKoszulMultiplication d := by
  apply DifferentialGraded.tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (exteriorKoszulMultiplication d).f n
    ((DifferentialGraded.signedSwap (exteriorKoszulCochain d)
      (exteriorKoszulCochain d)).hom.f n
        (ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
          p q n hn (x ⊗ₜ[R] y))) = _
  rw [DifferentialGraded.signedSwap_apply]
  change (exteriorKoszulMultiplication d).f n
    ((p * q).negOnePow •
      ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
        q p n (by omega) (y ⊗ₜ[R] x)) =
    (exteriorKoszulMultiplication d).f n
      (ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
        p q n hn (x ⊗ₜ[R] y))
  simp only [Units.smul_def, map_zsmul, exteriorKoszulMultiplication_apply]
  exact (exteriorCochainBilinear_comm d p q n hn x y).symm

end SerrePositivity.KST.DerivedBlowup
