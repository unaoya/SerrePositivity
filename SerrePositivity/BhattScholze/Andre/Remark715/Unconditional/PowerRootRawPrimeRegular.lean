module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.SourcePrimeConeTorsion
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.ScalarConeRestriction
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootRawPrimeConeCompletion
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootRawCoefficients

/-!
# 元の無限根モニック raw 包の p 正則性

## 概要
BS Rem 7.15（著者版 p.62）の正次数モニック入力について、元の raw 包は p 正則。

## 方針
元の実源の p 錐の d 冪ねじれ性と、その d 完備化の純性を合流する。
元の H⁰ 比較によって raw 包そのものへ移す。

## 規約
hpR と raw 包のねじれ除去を使わない。

## 使われ方
元の通常 p 完備化への正則性の保存に用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => PowerRootUnaryFreeDeltaRing A p hpNat
local notation "φ" => algebraMap A L
local notation "XL" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule (deltaDivisionSourceEval E a)),
    boundedAboveDerivedSingleFunctor.obj
      (baseChangeScalarModule (deltaDivisionSourceMap (σ := PUnit) E dP)))
local notation "X" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
local notation "Raw" => DeltaAdjoinDivision E dP a

set_option maxHeartbeats 800000 in
-- 元の実 A 係数作用と自由 δ 源上の p 錐を同じ係数制限として照合するため。
set_option backward.isDefEq.respectTransparency true in
/-- 概要：元の実 A 源の p 錐の非零次ホモロジーは、prism 生成元の冪ねじれ。
方針：自由 δ 源の局所化計算を、元の標準 A 作用へ係数制限する。
規約：モニック性・正次数・hpR は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw p 正則性検出。 -/
theorem powerRootPrismMonicSourcePrimeCone_power_torsion_of_unconditional
    (i : ℤ) (hi : i ≠ 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedScalarConeFunctor A (p : A)).obj (X).obj)) :
    ∃ n : ℕ, W.generator ^ n • x = 0 := by
  have hP : IsSMulRegular P (p : P) :=
    powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hT := unconditionalSourcePrimeCone_homology_power_torsion E dP a hP i hi
  have hT' : ∀ y : (DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      ((derivedScalarConeFunctor L (φ (p : A))).obj (XL).obj),
      ∃ n : ℕ, (φ W.generator) ^ n • y = 0 := by
    have hφp : φ (p : A) = (p : L) := map_natCast _ _
    have hφd : φ W.generator = (MvPolynomial.C dP : L) := rfl
    rw [hφp, hφd]
    with_reducible exact hT
  with_reducible exact (unconditionalBoundedRestrictionScalarCone_homology_power_torsion
    φ (p : A) W.generator XL i hT' x)

/-- 概要：正次数モニック入力の元の実 A 源の p 錐は負次数を持たない。
方針：元の p 錐の d 完備化純性と、同じ元の対象上の d 冪ねじれを合流する。
規約：hpR と raw p 正則性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の raw H⁰ の p 正則性。 -/
theorem powerRootPrismMonicSourcePrimeCone_isGE_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ((derivedScalarConeFunctor A (p : A)).obj (X).obj).IsGE 0 := by
  apply unconditional_isGE_of_completion_isGE_of_negative_power_torsion W.generator
  · exact powerRootPrismMonicSourcePrimeConeCompletion_isGE_of_unconditional W hW f hf hdeg
  · intro i hi
    exact powerRootPrismMonicSourcePrimeCone_power_torsion_of_unconditional W hW f i (by omega)

/-- 概要：正次数モニック入力の元の raw δ 包には p ねじれがない。
方針：元の実源の p 錐の負次数消滅を H⁰ 単射性へ移し、元の標準 raw 比較で運ぶ。
規約：元の raw 包を用い、hpR・ねじれ除去を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の通常 p 完備化への入力。 -/
theorem powerRootPrismMonicRaw_p_mul_injective_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  have hGE := powerRootPrismMonicSourcePrimeCone_isGE_of_unconditional W hW f hf hdeg
  have hinj := derived_homology_smul_injective_of_scalarCone_isZero (p : A) (X).obj 0
    ((DerivedCategory.isGE_iff _ 0).mp hGE (0 - 1) (by omega))
  let e := (powerRootPrismMonicSourceRawStandardH0Iso_of_unconditional W hW f).toLinearEquiv
  intro x y hxy
  apply e.symm.injective
  apply hinj
  change (p : A) • e.symm x = (p : A) • e.symm y
  rw [← e.symm.map_smul, ← e.symm.map_smul]
  apply congrArg e.symm
  simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hxy

end SerrePositivity.BhattScholze.Andre
