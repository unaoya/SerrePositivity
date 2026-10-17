module

public import SerrePositivity.BhattScholze.Andre.Unconditional.UnitNumeratorRawRegular
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawPrimeRegular
public import SerrePositivity.BhattScholze.Andre.PrincipalPairCompletionRegular

/-!
# 全モニック入力の元の raw 包と通常 p 完備化の p 正則性

## 概要
BS Rem 7.15（著者版 p.62）の元の raw p 正則性から hpR を除く。

## 方針
正次数入力では元の実源の純性を使う。次数零入力では f=1 と実安定局所化への単射性を使う。

## 規約
旧定理のモニック性を保持し、正次数を新たな仮定にしない。元の raw 包を用いる。

## 使われ方
元の通常 p 完備化の正則対への第一成分を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a

/-- 概要：次数零モニック入力でも元の raw 包は p 正則。
方針：f=1 と元の除算関係から、安定局所化への実単射を使う。
規約：元の raw 包を保持し、hpR は不要。
使われ方：BS Rem 7.15（著者版 p.62）の全モニック入力の合流。 -/
theorem powerRootPrismMonicRaw_p_mul_injective_of_natDegree_zero_unconditional
    (hf : f.Monic) (hz : f.natDegree = 0) :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
  have ha : ∃ s, a s = 1 := by
    refine ⟨(PUnit.unit : PUnit.{u + 1}), ?_⟩
    simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
  exact unconditionalRaw_prime_regular_of_unit_numerator E dP a
    (powerRootPolynomial_primeRegular p hW.p_mul_injective) ha

/-- 概要：任意のモニック入力の元の raw δ 包には p ねじれがない。
方針：正次数の実源純性と次数零の実安定局所化計算を合流する。
規約：旧公開定理から hpR だけを除き、正次数・完備性・ねじれ除去を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の通常 p 完備化への入力。 -/
theorem powerRootPrismMonicRaw_p_mul_injective_of_unconditional (hf : f.Monic) :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  by_cases hz : f.natDegree = 0
  · exact powerRootPrismMonicRaw_p_mul_injective_of_natDegree_zero_unconditional W hW f hf hz
  · exact powerRootPrismMonicRaw_p_mul_injective_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：任意モニック入力の元の古典的 p 完備化でも p は正則。
方針：元の raw p 正則性を古典的主完備化の正則性保存に渡す。
規約：元の AdicCompletion を保持し、hpR は不要。
使われ方：BS Rem 7.15（著者版 p.62）の通常 p 完備化の正則対の第一成分。 -/
theorem powerRootPrismMonicRaw_pAdic_prime_regular_of_unconditional (hf : f.Monic) :
    let C := AdicCompletion (Ideal.span {(p : Raw)}) Raw
    IsSMulRegular C (p : C) := by
  simpa only [map_natCast] using isSMulRegular_adicCompletion_span_singleton Raw (p : Raw)
    (powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf)

end SerrePositivity.BhattScholze.Andre
