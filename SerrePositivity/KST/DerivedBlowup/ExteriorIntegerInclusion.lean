module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainInclusion

/-!
概要：KST Def3.1 の整数次数複体の全項を総外積代数へ単射で写す。
方針：非正次数では第−q外積への標準同型、正次数では零対象性を使う。
規約：cochain 次数qに対応する外積次数は (−q).toNat。
使われ方：全ての整数双次数を扱う Koszul の乗法の構成。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：任意の非正整数次数の項を対応する外積と同定する。
方針：埋め込みの逆添字として (−q).toNat を取る。
規約：KST Def3.1。使われ方：非正双次数の積を定義する標準同型。 -/
def exteriorCochainXIsoNonpos (d : M →ₗ[R] R) (q : ℤ) (hq : q ≤ 0) :
    (exteriorKoszulCochain d).X q ≅
      ModuleCat.of R (ExteriorAlgebra.exteriorPower R (-q).toNat M) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (by
    simp only [ComplexShape.embeddingUpIntLE_f, zero_sub]
    omega)

/-- 概要：各整数次数の項から総外積への線形包含。
方針：非正次数の同型と部分加群包含を合成し、正次数は零写像。
規約：KST Def3.1、正次数の項は零対象。使われ方：全整数次数の積と微分の計算。 -/
def exteriorCochainInclusion (d : M →ₗ[R] R) (q : ℤ) :
    (exteriorKoszulCochain d).X q →ₗ[R] ExteriorAlgebra R M :=
  if hq : q ≤ 0 then
    (ExteriorAlgebra.exteriorPower R (-q).toNat M).subtype.comp
      (exteriorCochainXIsoNonpos d q hq).hom.hom
  else 0

/-- 概要：負の自然数次数では既存の包含と一致する。
方針：逆添字 (−(−n)).toNat を簡約する。
規約：KST Def3.1。使われ方：収縮微分との比較を全整数次数へ延長する。 -/
@[simp] theorem exteriorCochainInclusion_neg (d : M →ₗ[R] R) (n : ℕ) :
    exteriorCochainInclusion d (-(n : ℤ)) = exteriorCochainInclusionNeg d n := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- 概要：全整数次数の包含は単射。
方針：非正次数では同型と部分加群包含、正次数では定義域の零対象性。
規約：KST Def3.1。使われ方：総外積の等式で複体の chain 条件を検証する。 -/
theorem exteriorCochainInclusion_injective (d : M →ₗ[R] R) (q : ℤ) :
    Function.Injective (exteriorCochainInclusion d q) := by
  by_cases hq : q ≤ 0
  · simp only [exteriorCochainInclusion, hq, dite_true]
    exact Subtype.val_injective.comp
      ((ModuleCat.mono_iff_injective (exteriorCochainXIsoNonpos d q hq).hom).mp inferInstance)
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq))
    exact fun _ _ _ => Subsingleton.elim _ _

/-- 概要：各項の像は対応する同次外積に属する。
方針：非正次数では部分加群条件、正次数では零元。
規約：KST Def3.1。使われ方：双次数の積の同次性の証明。 -/
theorem exteriorCochainInclusion_mem (d : M →ₗ[R] R) (q : ℤ)
    (z : (exteriorKoszulCochain d).X q) :
    exteriorCochainInclusion d q z ∈ ExteriorAlgebra.exteriorPower R (-q).toNat M := by
  by_cases hq : q ≤ 0
  · simp only [exteriorCochainInclusion, hq, dite_true]
    exact ((exteriorCochainXIsoNonpos d q hq).hom.hom z).property
  · simp only [exteriorCochainInclusion, hq, dite_false, LinearMap.zero_apply]
    exact Submodule.zero_mem _

end SerrePositivity.KST.DerivedBlowup
