module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Localization
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Source
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalPair

/-!
# raw 包と主完備化の p 正則性

## 概要
無限根モニック raw 包・全モニック入力の raw 包と通常 p 完備化の p 正則性、第一完備化の分母正則性と H⁰、正則対からの hpR の除去。
BS 著者版 Corollary 2.39 と Remark 7.15 の包の比較に向けて、raw 包と主完備化の p 正則性を示す。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPrism`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## 元の無限根モニック raw 包の p 正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の正次数モニック入力について、元の raw 包は p 正則。

## 方針
元の実源の p 錐の d 冪ねじれ性と、その d 完備化の純性を合流する。
元の H⁰ 比較によって raw 包そのものへ移す。

## 規約
hpR と raw 包のねじれ除去を使わない。

## 使われ方
元の通常 p 完備化への正則性の保存に用いる。
-/

@[expose] public noncomputable section PowerRootRawPrimeRegular

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw p 正則性検出。 -/
theorem powerRootPrismMonicSourcePrimeCone_power_torsion_of_unconditional
    (i : ℤ) (hi : i ≠ 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((derivedScalarConeFunctor A (p : A)).obj (X).obj)) :
    ∃ n : ℕ, W.generator ^ n • x = 0 := by
  have hP : IsSMulRegular P (p : P) :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の raw H⁰ の p 正則性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の通常 p 完備化への入力。 -/
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

end PowerRootRawPrimeRegular

/-! ## 全モニック入力の元の raw 包と通常 p 完備化の p 正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の raw p 正則性から hpR を除く。

## 方針
正次数入力では元の実源の純性を使う。次数零入力では f=1 と実安定局所化への単射性を使う。

## 規約
旧定理のモニック性を保持し、正次数を新たな仮定にしない。元の raw 包を用いる。

## 使われ方
元の通常 p 完備化の正則対への第一成分を供給する。
-/

@[expose] public noncomputable section RawPrimeRegularAllMonic

namespace SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a

/-- 概要：次数零モニック入力でも元の raw 包は p 正則。
方針：f=1 と元の除算関係から、安定局所化への実単射を使う。
規約：元の raw 包を保持し、hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全モニック入力の合流。 -/
theorem powerRootPrismMonicRaw_p_mul_injective_of_natDegree_zero_unconditional
    (hf : f.Monic) (hz : f.natDegree = 0) :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
  have ha : ∃ s, a s = 1 := by
    refine ⟨(PUnit.unit : PUnit.{u + 1}), ?_⟩
    simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
  exact unconditionalRaw_prime_regular_of_unit_numerator E dP a
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomial_primeRegular p hW.p_mul_injective) ha

/-- 概要：任意のモニック入力の元の raw δ 包には p ねじれがない。
方針：正次数の実源純性と次数零の実安定局所化計算を合流する。
規約：旧公開定理から hpR だけを除き、正次数・完備性・ねじれ除去を追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の通常 p 完備化への入力。 -/
theorem powerRootPrismMonicRaw_p_mul_injective_of_unconditional (hf : f.Monic) :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  by_cases hz : f.natDegree = 0
  · exact powerRootPrismMonicRaw_p_mul_injective_of_natDegree_zero_unconditional W hW f hf hz
  · exact powerRootPrismMonicRaw_p_mul_injective_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：任意モニック入力の元の古典的 p 完備化でも p は正則。
方針：元の raw p 正則性を古典的主完備化の正則性保存に渡す。
規約：元の AdicCompletion を保持し、hpR は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常 p 完備化の正則対の第一成分。 -/
theorem powerRootPrismMonicRaw_pAdic_prime_regular_of_unconditional (hf : f.Monic) :
    let C := AdicCompletion (Ideal.span {(p : Raw)}) Raw
    IsSMulRegular C (p : C) := by
  simpa only [map_natCast] using isSMulRegular_adicCompletion_span_singleton Raw (p : Raw)
    (powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf)

end SerrePositivity.BhattScholze.Andre

end RawPrimeRegularAllMonic

/-! ## 元の第一完備化の分母正則性

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実 p 完備化の H⁰ で分母は正則。

## 方針
d 完備化単位の実 d 錐同値性から、既証明の逐次完備化の分母正則性を戻す。

## 規約
元の実源と標準 A 作用を保持し、raw mod p の d 正則性を使わない。

## 使われ方
元の通常 p 完備化の分母正則性へ移す。
-/

@[expose] public noncomputable section PrincipalSourceRegularity

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：完備化が正則主元を持つ single なら、元の H⁰ 上でも同じ主元は単射。
方針：元の完備化単位の Koszul 同値性と、加群上の正則主商の実錐比較を使う。
規約：元の対象の純性・完備性・環の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の第一完備化への分母正則性の移送。 -/
theorem unconditionalHomology_regular_of_completionSingleIso
    {R : Type u} [CommRing R] (a : R) (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (M : ModuleCat.{u} R)
    (e : (derivedComplexCompletionFunctor R a).obj X.obj ≅
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)
    (hM : IsSMulRegular M a) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => a • x) := by
  let η := (derivedComplexCompletionUnit R a).app X.obj
  have hη := derivedScalarCone_map_isIso_of_completion R a η
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) 1
  rw [pow_one] at hη
  have := hη
  have eQ := derivedScalarConeModuleQuotientIso a M hM 1
  rw [pow_one] at eQ
  let eC := asIso ((derivedScalarConeFunctor R a).map η) ≪≫
    (derivedScalarConeFunctor R a).mapIso e ≪≫ eQ
  apply derived_homology_smul_injective_of_scalarCone_isZero a X.obj 0
  exact (derivedSingleHomology_isZero (modulePowerReduction a M 1) (0 - 1) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) (0 - 1)).mapIso eC)

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "X" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
local notation "XP" => CategoryTheory.Functor.obj
  (boundedAboveDerivedCompletionFunctor A (p : A)) (X)
local notation "XC" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f

/-- 概要：正次数モニック入力の元の実 p 完備化の H⁰ 上で分母は単射。
方針：同じ実源の逐次完備化の single 比較と分母正則性を一般の Koszul 比較へ渡す。
規約：hpR・raw mod p の分母正則性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の古典的 p 完備化の分母正則性。 -/
theorem powerRootPrismMonicSourcePCompletion_generator_injective_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XP).obj => W.generator • x) :=
  unconditionalHomology_regular_of_completionSingleIso W.generator XP
    ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XC).obj)
    (powerRootPrismMonicSourceSingleIso_of_unconditional W hW f hf hdeg)
    (powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional W hW f hf hdeg).2.2

end SerrePositivity.BhattScholze.Andre

end PrincipalSourceRegularity

/-! ## 元の第一完備化の H⁰ と raw の主完備化

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の元の実源の第一 p 完備化の H⁰ を、raw 主完備化へ比較する。

## 方針
元の標準 augmentation、正確な係数制限と完備化の比較、実主 Koszul H⁰ 比較を合成する。

## 規約
元の標準 A 作用を保持する。モニック性・正次数は比較自体には不要。

## 使われ方
元の古典的 p 完備化へ分母正則性を移す。
-/

@[expose] public noncomputable section RawPrincipalH0Comparison

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "c" => algebraMap A Raw
local notation "X" => PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f
local notation "XP" => CategoryTheory.Functor.obj
  (boundedAboveDerivedCompletionFunctor A (p : A)) (X)

/-- 概要：元の実源の第一 p 完備化の H⁰ と、元の raw 主完備化の A 線形同型。
方針：元の標準 augmentation の完備化後 H⁰ 同型と、元の主完備化の比較を合成する。
規約：比較自体には raw p 正則性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分母作用の元の古典的 p 完備化への移送。 -/
def powerRootPrismMonicSourcePrincipalH0Iso_of_unconditional :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (XP).obj ≅
      (ModuleCat.restrictScalars c).obj
        (ModuleCat.of Raw (PrincipalCompletionH0 Raw (p : Raw))) := by
  let M := (DerivedCategory.singleFunctor (ModuleCat Raw) 0).obj (ModuleCat.of Raw Raw)
  let F := derivedComplexCompletionFunctor A (p : A)
  have hAug := powerRootPrismMonicSourceRawPComparison_h0_isIso_of_unconditional W hW f
  let eAug := asIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
    (((boundedAboveDerivedCompletionFunctor A (p : A)).map
      (powerRootPrismMonicSourceRawCoefficientAugmentation_of_unconditional W hW f)).hom))
  let eP := F.mapIso (powerRootPrismMonicRawCoefficientRestrictionIso_of_unconditional W hW f) ≪≫
    (derivedCompletionRestrictionIso c (p : A)).app M
  rw [map_natCast] at eP
  let eH := (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso eP ≪≫
    (derivedRestrictScalarsHomologyIso c 0).app
      ((derivedComplexCompletionFunctor Raw (p : Raw)).obj M)
  let eN : (DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
      ((derivedComplexCompletionFunctor Raw (p : Raw)).obj M) ≅
        ModuleCat.of Raw (PrincipalCompletionH0 Raw (p : Raw)) :=
    principalCompletedUnitH0Iso Raw (p : Raw)
  exact eAug ≪≫ eH ≪≫ (ModuleCat.restrictScalars c).mapIso eN

end SerrePositivity.BhattScholze.Andre

end RawPrincipalH0Comparison

/-! ## 元の通常 p 完備化の正則対から hpR を除く

## 概要
BS 著者版 Remark 7.15（著者版 p.62）の任意モニック入力について、元の通常 p 完備化で p と分母は正則。

## 方針
元の実第一完備化の H⁰ 比較で分母正則性を移し、次数零では元の分母の単元性を使う。

## 規約
元の AdicCompletion と標準係数射を保持する。raw mod p の分母正則性を仮定しない。

## 使われ方
旧 powerRootPrismMonicRaw_pAdic_regular_pair の hpR なしの置換先。
-/

@[expose] public noncomputable section RawPAdicPairRegular

namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：係数制限を保つ線形同型は、元の基底元の正則性を標準代数像へ移す。
方針：同じ線形同型の逆で単射性を運び、標準スカラー作用を乗法へ書き直す。
規約：基底射の単射性・平坦性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的な古典的完備化の作用の照合。 -/
theorem unconditionalRegularity_of_restricted_linearEquiv
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S] [Algebra R S]
    (c : A →+* R) (M : ModuleCat.{u} A)
    (e : M ≃ₗ[A] (ModuleCat.restrictScalars c).obj (ModuleCat.of R S))
    (d : A) (hd : IsSMulRegular M d) : IsSMulRegular S (algebraMap R S (c d)) := by
  intro x y hxy
  apply e.symm.injective
  apply hd
  change d • e.symm x = d • e.symm y
  rw [← e.symm.map_smul, ← e.symm.map_smul]
  apply congrArg e.symm
  change (c d) • x = (c d) • y
  simpa only [smul_eq_mul, Algebra.smul_def] using hxy

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hpNat
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "c" => algebraMap A Raw
local notation "C" => AdicCompletion (Ideal.span {(p : Raw)}) Raw

/-- 概要：正次数モニック入力では元の通常 p 完備化の分母像が正則。
方針：元の実第一完備化 H⁰ の分母正則性を、標準 raw 主完備化比較で移す。
規約：hpR と raw mod p の分母正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の通常 p 完備化の正則対。 -/
theorem powerRootPrismMonicRaw_pAdic_generator_regular_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsSMulRegular C (algebraMap Raw C (j dP)) := by
  let := principalCompletionCommRing Raw (p : Raw)
  let := principalCompletionAlgebra Raw (p : Raw)
  have hpRaw : IsSMulRegular Raw (p : Raw) :=
    powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf
  let eC := (principalCompletionAdicAlgEquiv Raw (p : Raw) hpRaw).toLinearEquiv.toModuleIso
  let e := (powerRootPrismMonicSourcePrincipalH0Iso_of_unconditional W hW f ≪≫
    (ModuleCat.restrictScalars c).mapIso eC).toLinearEquiv
  have hsrc := powerRootPrismMonicSourcePCompletion_generator_injective_of_positive_unconditional
    W hW f hf hdeg
  exact unconditionalRegularity_of_restricted_linearEquiv c _ e W.generator hsrc

/-- 概要：任意モニック入力では元の通常 p 完備化の分母像が正則。
方針：正次数の実第一完備化計算と、f=1 の場合の元の分母の単元性を合流する。
規約：旧主張のモニック性だけを保持し、hpR を除く。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の通常 p 完備化の正則対。 -/
theorem powerRootPrismMonicRaw_pAdic_generator_regular_of_unconditional (hf : f.Monic) :
    IsSMulRegular C (algebraMap Raw C (j dP)) := by
  by_cases hz : f.natDegree = 0
  · have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
    have ha : ∃ s, a s = 1 := by
      refine ⟨(PUnit.unit : PUnit.{u + 1}), ?_⟩
      simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
    exact ((unconditionalRaw_denominator_isUnit_of_unit_numerator E dP a ha).map
      (algebraMap Raw C)).mul_right_injective
  · exact powerRootPrismMonicRaw_pAdic_generator_regular_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：元の通常 p 完備化で p と分母はともに正則。
方針：元の raw p 正則性の完備化保存と、元の実源から移した分母正則性を合流する。
規約：旧公開定理と同じ対象・標準射で hpR だけを除く。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実二座標完備化への入力。 -/
theorem powerRootPrismMonicRaw_pAdic_regular_pair_of_unconditional (hf : f.Monic) :
    let CP := AdicCompletion (Ideal.span {(p : Raw)}) Raw
    IsSMulRegular CP (p : CP) ∧ IsSMulRegular CP (algebraMap Raw CP (j dP)) := by
  exact ⟨powerRootPrismMonicRaw_pAdic_prime_regular_of_unconditional W hW f hf,
    powerRootPrismMonicRaw_pAdic_generator_regular_of_unconditional W hW f hf⟩

end SerrePositivity.BhattScholze.Andre

end RawPAdicPairRegular
