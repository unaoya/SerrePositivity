module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainProduct
public import SerrePositivity.KST.DerivedBlowup.ExteriorLeibniz
public import Mathlib.Algebra.Ring.NegOnePow

/-!
概要：KST Def3.1 の双次数乗法が整数 cochain 微分の Leibniz 則を満たすことを示す。
方針：単射な総外積への包含で検証し、外積次数の符号を Int.negOnePow に合わせる。
規約：tensor の第一因子の cochain 次数が符号を決める。
使われ方：Koszul 乗法を全 tensor からの chain map に持ち上げる。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：非正 cochain 次数の単元符号を外積次数の基底環スカラーへ移す。
方針：整数スカラーの基底環への移送と negOnePow の natAbs 表示を使う。
規約：KST Def3.1、q≤0。使われ方：Leibniz 則と tensor 微分の符号比較。 -/
theorem exteriorCochain_sign (q : ℤ) (hq : q ≤ 0) (z : ExteriorAlgebra R M) :
    q.negOnePow • z = (-1 : R) ^ (-q).toNat • z := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, Int.coe_negOnePow]
  have hn : q.natAbs = (-q).toNat := by omega
  rw [hn]

/-- 概要：双次数 Koszul 乗法の微分は整数 cochain Leibniz 則を満たす。
方針：単射な包含を通して全外積代数の Leibniz 則に帰着する。
規約：KST Def3.1、符号は第一因子の次数p。
使われ方：tensorLift の乗法の chain 条件。 -/
theorem exteriorCochainBilinear_d (d : M →ₗ[R] R) (p q n : ℤ) (h : p + q = n)
    (x : (exteriorKoszulCochain d).X p) (y : (exteriorKoszulCochain d).X q) :
    ((exteriorKoszulCochain d).d n (n + 1)).hom (exteriorCochainBilinear d p q n h x y) =
      exteriorCochainBilinear d (p + 1) q (n + 1) (by omega)
          (((exteriorKoszulCochain d).d p (p + 1)).hom x) y +
        p.negOnePow • exteriorCochainBilinear d p (q + 1) (n + 1) (by omega)
          x (((exteriorKoszulCochain d).d q (q + 1)).hom y) := by
  apply exteriorCochainInclusion_injective d (n + 1)
  rw [exteriorCochainInclusion_d, exteriorCochainInclusion_product, map_add]
  simp only [Units.smul_def, map_zsmul]
  rw [exteriorCochainInclusion_product, exteriorCochainInclusion_product,
    exteriorCochainInclusion_d, exteriorCochainInclusion_d]
  by_cases hp : p ≤ 0
  · have hl := exteriorContraction_mul d (-p).toNat (exteriorCochainInclusion d p x)
      (exteriorCochainInclusion_mem d p x) (exteriorCochainInclusion d q y)
    rw [← exteriorCochain_sign p hp] at hl
    exact hl
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d p (lt_of_not_ge hp))
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp only [map_zero, zero_mul, zero_add, smul_zero]

end SerrePositivity.KST.DerivedBlowup
