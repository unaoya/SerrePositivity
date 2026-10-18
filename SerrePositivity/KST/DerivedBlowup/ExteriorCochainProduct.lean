module

public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerDifferential
public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeProduct

/-!
概要：KST Def3.1 の整数次数外積複体の双次数乗法を構成する。
方針：非正次数では同次外積を標準同型で移し、正次数の零項では零にする。
規約：この段階は双線形成分であり、全 tensor からの chain map は次の段階。
使われ方：Koszul チャートの dg 代数としての乗法。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：第−q外積の元を項へ戻してから包含すると元に戻る。
方針：標準同型の逆元律。規約：KST Def3.1。
使われ方：双次数乗法を総外積代数の積と比較する。 -/
@[simp] theorem exteriorCochainInclusion_inv (d : M →ₗ[R] R) (q : ℤ) (hq : q ≤ 0)
    (z : ExteriorAlgebra.exteriorPower R (-q).toNat M) :
    exteriorCochainInclusion d q ((exteriorCochainXIsoNonpos d q hq).inv.hom z) = z.val := by
  rw [exteriorCochainInclusion, dite_eq_left hq]
  change ((exteriorCochainXIsoNonpos d q hq).hom.hom
    ((exteriorCochainXIsoNonpos d q hq).inv.hom z)).val = z.val
  exact congrArg Subtype.val ((exteriorCochainXIsoNonpos d q hq).toLinearEquiv.apply_symm_apply z)

/-- 概要：整数双次数の Koszul 乗法の双線形成分。
方針：非正次数の同次積を標準同型で移す。
規約：KST Def3.1、p+q=n を明示。使われ方：tensorLift に渡す乗法成分。 -/
def exteriorCochainBilinear (d : M →ₗ[R] R) (p q n : ℤ) (h : p + q = n) :
    (exteriorKoszulCochain d).X p →ₗ[R]
      (exteriorKoszulCochain d).X q →ₗ[R] (exteriorKoszulCochain d).X n :=
  if hp : p ≤ 0 then
    if hq : q ≤ 0 then
      let hn : n ≤ 0 := by omega
      let hd : (-p).toNat + (-q).toNat = (-n).toNat := by omega
      ((exteriorDegreeProduct (-p).toNat (-q).toNat (-n).toNat hd).compl₁₂
        (exteriorCochainXIsoNonpos d p hp).hom.hom
        (exteriorCochainXIsoNonpos d q hq).hom.hom).compr₂
          (exteriorCochainXIsoNonpos d n hn).inv.hom
    else 0
  else 0

/-- 概要：複体の双次数積は総外積代数での通常の積に写る。
方針：非正次数では標準同型の往復、正次数では零対象性を使う。
規約：KST Def3.1。使われ方：Leibniz 則と結合則を単射な包含で検証する。 -/
theorem exteriorCochainInclusion_product (d : M →ₗ[R] R) (p q n : ℤ) (h : p + q = n)
    (x : (exteriorKoszulCochain d).X p) (y : (exteriorKoszulCochain d).X q) :
    exteriorCochainInclusion d n (exteriorCochainBilinear d p q n h x y) =
      exteriorCochainInclusion d p x * exteriorCochainInclusion d q y := by
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · simp only [exteriorCochainBilinear, hp, hq, dite_true,
        LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
      rw [exteriorCochainInclusion_inv]
      simp only [exteriorDegreeProduct_val, exteriorCochainInclusion, hp, hq, dite_true]
      rfl
    · have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq))
      have hy : y = 0 := Subsingleton.elim _ _
      subst y
      simp only [map_zero, mul_zero]
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d p (lt_of_not_ge hp))
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp only [map_zero, LinearMap.zero_apply, zero_mul]

end SerrePositivity.KST.DerivedBlowup
