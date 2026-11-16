module

public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import Mathlib.Algebra.Polynomial.Lifts
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicSource
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue

/-!
# 完全 prism 商上の有限モニック族の根付き拡大（BS 著者版 Theorem 7.14 の一段目 R ↦ R₁）

## 概要
完全 prism の商からのモニック根候補、完備化源の離散性、raw PD 環と既存 prism 候補の完全忠実平坦性、δ 完全化への入力、候補の剰余と perfectoid 商、標準 perfectoid 候補の p 完全忠実平坦性、完全 prism 商上の根付き拡大。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Transfinite/Tower`、`Variants/ArbitraryFamily`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u

/-! ## André：完全 prism の商からのモニック根候補

## 概要

完全 prism の商上のモニック多項式族を、次数とモニック性を保って prism の台環へ持ち上げ、
具体的な perfectoid 根候補を得る。BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の準備。

## 方針

モニック係数 lift の Mathlib の定理を使い、前工程の多項式族の候補を適用する。
係数商からの基底射を保ったまま評価の自然性で根方程式を移す。
原典の BS 著者版 Proposition 7.11 による証明とは異なる δ 除算の経路である。

## 規約

候補の忠実平坦性は未証明であり、最終目標を宣言するものではない。
ここでは正次数は不要で、零環の候補を排除しない。

## 使われ方

同じモニック lift の正則性と pd 計算を使い、候補の p 完全忠実平坦性を後で供給する。
-/

@[expose] public noncomputable section PerfectPrismMonicCandidate

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A)

local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}
local notation "q" => Ideal.Quotient.mk (Ideal.span {OrientedPrism.generator P})

/-- 概要：商上のモニック多項式族を同次数モニックに lift する。
方針：商係数射の全射性とモニック lift の存在定理から選ぶ。
規約：lift の選択を固定し、後の候補と正則性で同じものを使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の prismatic envelope の関係式。 -/
def perfectPrismMonicLift (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) :
    σ → Polynomial A := fun s =>
  Classical.choose (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))

/-- 概要：固定した lift は係数商射で元の多項式に写る。
方針：lift の選択の証明を取り出す。
規約：基底係数作用を変えない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の元の多項式の根方程式。 -/
theorem perfectPrismMonicLift_map (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (s : σ) :
    (perfectPrismMonicLift P f hf s).map q = f s :=
  (Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))).1

/-- 概要：固定した lift は元の多項式と同じ次数を持つモニックである。
方針：同次数モニック lift の選択の証明を取り出す。
規約：元が正次数なら lift も正次数となる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック商・正則性。 -/
theorem perfectPrismMonicLift_spec (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (s : σ) :
    (perfectPrismMonicLift P f hf s).natDegree = (f s).natDegree ∧
      (perfectPrismMonicLift P f hf s).Monic :=
  (Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))).2

/-- 概要：完全 prism の商上のモニック族には、具体的な根を持つ perfectoid 候補がある。
方針：同次数モニック lift の関係式を δ 除算し、商射と評価の自然性で根を降ろす。
規約：p 完全忠実平坦性は未証明であり、零候補を許す。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の別経路で同じ候補の平坦性を後で検証する。 -/
theorem exists_monicRootedPerfectoidCandidate_of_perfectPrism
    (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧ ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let F := perfectPrismMonicLift P f hf
  let hd := OrientedPrism.isDistinguished_generator P
  let D := P.deltaStructure
  let d := P.generator
  let := polynomialPrismCommRing D d F
  let φ := polynomialPerfectoidCandidateBaseMap D d F hd
  let ρ := polynomialPerfectoidCandidateRoot D d F hd
  refine ⟨PolynomialPerfectoidCandidate D d F hd, inferInstance, φ, ρ,
    polynomialPerfectoidCandidate_isIntegralPerfectoid D d F hd, ?_⟩
  intro s
  rw [← perfectPrismMonicLift_map P f hf s, Polynomial.eval₂_map]
  exact polynomialPerfectoidCandidate_eval D d F hd s

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicCandidate

/-! ## 完全 prism 上の有限モニック族の実完備化源の離散性

## 概要

完全 prism 上の有限正次数モニック族の一般 f/d 源を p,d の順に実導来完備化すると離散的となる。
BS 著者版 Remark 7.15（著者版 p.62）の実 prismatic envelope 比較への入力。

## 方針

完全 prism の生成元冪商の p 冪ねじれ上界と、標準 mod p 還元の離散・平坦性から 離散性の判定 を適用する。
その生成元商の離散性と d 導来完備性から元の対象の純性を得る。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

有限全列挙と正次数モニック性を要求する。最終 perfectoid 商との環同型は別工程。

## 使われ方

同じ実 H⁰ を raw PD 完備化環へ比較して、元の係数射の完全忠実平坦性を導く。
-/

@[expose] public noncomputable section PerfectPrismMonicSourceDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
include hP hf hdeg s

/-- 概要：完全 prism 上の有限モニック族の実完備化源の正の生成元冪商は離散的。
方針：標準 mod p の離散・平坦性、p 導来完備性、生成元冪商の p 冪ねじれ上界を 離散性の判定 へ渡す。
規約：d mod p の正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の実完備化対象の離散性。 -/
theorem perfectPrismMonicSourcePower_pure (n : ℕ) (hn : 0 < n) :
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 := by
  let T := A ⧸ Ideal.span {d ^ n}
  let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  obtain ⟨hc, hz, hflat⟩ := monicPrismaticSourceGeneratorPower_G9_inputs D d f n hn
    hf hdeg s hP.p_mul_injective P.generator_regular v hv
  have hbound : ∃ N : ℕ, ∀ k : ℕ, ∀ x : T,
      (p : T) ^ k * x = 0 → (p : T) ^ N * x = 0 := by
    let := P.isAdicComplete_p_of_perfect hP
    exact ⟨n, fun k x hx => hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
      (P.isDistinguished_generator) n k x hx⟩
  exact derived_pure_of_complete_flat_reduction (p : T) Z hz hflat hbound hc

/-- 概要：完全 prism 上の有限モニック族の実逐次 p,d 完備化源は離散的。
方針：生成元商の離散性、生成元の正則性、d 導来完備性を一般純性判定へ渡す。
規約：同じ元の係数環上の実対象を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ を環候補へ比較する。 -/
theorem perfectPrismMonicSource_pure : (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    have hpow := perfectPrismMonicSourcePower_pure P hP f hf hdeg s 1 (by omega)
    dsimp only at hpow
    rw [pow_one] at hpow
    rcases lt_or_gt_of_ne hi with h | h
    · exact (DerivedCategory.isGE_iff _ _).mp hpow.1 i h
    · exact (DerivedCategory.isLE_iff _ _).mp hpow.2 i h
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (monicPrismaticSourceIteratedPDCompletion_isComplete_d D d f) hmod
  exact ⟨hGE, hLE⟩

/-- 概要：同じ実逐次完備化源の全非零次数ホモロジーは零。
方針：純性を標準 t 構造のホモロジー消滅として展開する。
規約：全非零整数次数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数射の実還元計算への接続。 -/
theorem perfectPrismMonicSource_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure P hP f hf hdeg s
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：実完備化源は同じ実 H⁰ の single と正規化された同型を持つ。
方針：標準 t 構造の純対象の既存正規化比較を使う。
規約：元の A 作用と実 H⁰ を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較へ渡す。 -/
def perfectPrismMonicSourceSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure P hP f hf hdeg s
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicSourceDiscrete

/-! ## 有限モニック族の raw 実 PD 環の完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の raw f/d 包の実 PD 完備化環は、元の (p,d) に関して
完全忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の環候補への平坦性の移送。

## 方針

同じ実源の離散性と、元の係数作用を保つ H⁰ 比較から raw PD 環の single 比較を構成する。
実剰余の Tor 消滅と忠実平坦性を完全忠実平坦性の一般判定へ渡す。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

この raw PD 環の完全 δ 化と最終 perfectoid 商への比較は別工程。

## 使われ方

完全 δ 化と実完備化の既存比較を介して、最終根付き perfectoid 候補の平坦性へ進む。
-/

@[expose] public noncomputable section PerfectPrismMonicRawPDCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hP hf hdeg s

/-- 概要：元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
def perfectPrismMonicSourcePDSingleIso : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (perfectPrismMonicSourceSingleIso P hP f hf hdeg s ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (monicPrismaticSourcePDH0Iso D d f))

/-- 概要：実PD環の同じ(p,d)導来還元の非零次数は消える。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  have hz := monicPrismaticSourceIteratedPDResidue_homology_isZero D d f s hf
    hP.p_mul_injective P.generator_regular v hv i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso
        (perfectPrismMonicSourcePDSingleIso P hP f hf hdeg s)))).symm

/-- 概要：実PD環の同じ(p,d)導来還元のH0は忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reductionH0_faithfullyFlat :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_generator
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat D d f s hf hdeg
    hP.p_mul_injective P.generator_regular v hv
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (perfectPrismMonicSourcePDSingleIso P hP f hf hdeg s)))).toLinearEquiv.symm

/-- 概要：実PD環の具体的A係数加群の(p,d)高次Torは零。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_torVanishing : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismMonicRawPD_reduction_homology_isZero P hP f hf hdeg s (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 概要：実PD環の通常係数拡大も同じ商環上忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_scalarExtension_faithfullyFlat :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat P hP f hf hdeg s
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 概要：有限正次数モニック族のraw実PD環は、元の(p,d)に関して完全忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismMonicRawPD_scalarExtension_faithfullyFlat P hP f hf hdeg s
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismMonicRawPD_torVanishing P hP f hf hdeg s) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicRawPDCompletelyFlat

/-! ## raw モニック PD 環の δ 完全化への平坦性入力

## 概要

完全 prism 上の有限正次数モニック族の raw PD 環の標準係数射は δ 射で、
その δ 完全化の実 PD 完備化は元の (p,d) に関して完全忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への準備。

## 方針

raw PD 環の元の係数制限作用を標準環射の作用に同定し、既存の一般 δ 代数の定理を適用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる具体的な係数射の計算。

## 規約

完全化の対象は明示的に固定する。最終 f/d 候補との環比較と perfectoid 商は別工程。

## 使われ方

一般の完備化・δ 完全化の比較同型を介して、最終根付き候補へ完全忠実平坦性を移す。
-/

@[expose] public noncomputable section PerfectPrismMonicPDPerfectionInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
section Coefficients
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

/-- 概要：実PD係数加群は、元の標準環射A→PDに沿う制限加群そのものである。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
def monicPrismaticPDSourceModuleIso :
    letI := pdCompletionCommRing Raw p z
    M ≅ baseChangeScalarModule j := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionAlgebra Raw p z
  let Mc : ModuleCat.{u} A := M
  let Nc : ModuleCat.{u} A := baseChangeScalarModule j
  let f : Mc →ₗ[A] Nc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change (c a) • x = s (c a) * x
        exact Algebra.smul_def (c a) x }
  let g : Nc →ₗ[A] Mc :=
    { toFun := (id : B → B)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        change s (c a) * x = (c a) • x
        exact (Algebra.smul_def (c a) x).symm }
  let e : Mc ≃ₗ[A] Nc := LinearEquiv.ofLinearMap f g (by ext x; rfl) (by ext x; rfl)
  exact e.toModuleIso

/-- 概要：同じ標準PD係数射は、元のδ構造からのδ射。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem monicPrismaticPDSourceCoefficient_isDeltaHom :
    letI := pdCompletionCommRing Raw p z
    D.IsDeltaHom G j := by
  let := pdCompletionCommRing Raw p z
  exact (pdCompletionUnit_isDeltaHom F z).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

end Coefficients

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor (baseChangeScalarModule j))

include hP hf hdeg eσ

/-- 概要：完全prism上では、同じPD係数射に沿う実還元の非零次数は消える。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing Raw p z
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  have hz := perfectPrismMonicRawPD_reduction_homology_isZero P hP f hf hdeg eσ i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso (monicPrismaticPDSourceModuleIso D d f))))).symm

/-- 概要：同じ標準PD係数射に沿う実還元のH0は忠実平坦。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDSource_reductionH0_faithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing Raw p z
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat P hP f hf hdeg eσ
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (monicPrismaticPDSourceModuleIso D d f))))).toLinearEquiv.symm

/-- 概要：有限正次数モニック族の実PD環のδ完全化を逐次実完備化した具体的対象は離散。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionCompletion_pure :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletion_pure P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero P hP f hf hdeg eσ)
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat P hP f hf hdeg eσ)

/-- 概要：同じ具体的δ完全化逐次対象の生成元冪商も離散でH0のp冪ねじれは有界。
方針：raw PD 環の元の係数作用を標準環射の作用に同定し、一般 δ 完全化の定理へ渡す。
規約：係数作用の比較自体にはモニック性は不要。完全 prism 上の適用には有限正次数モニック族を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終完全 prism 候補への移送。 -/
theorem perfectPrismMonicPDPerfectionPower_pure_bounded_torsion (n : ℕ) (hn : 0 < n) :
    letI := pdCompletionCommRing Raw p z
    let X := DeltaAlgebraPerfectionIteratedPDCompletion G j d
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • x = 0 → (p : T) ^ N • x = 0 := by
  let := pdCompletionCommRing Raw p z
  exact perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero P hP f hf hdeg eσ)
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat P hP f hf hdeg eσ) n hn

local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ

/-- 概要：有限正次数モニック族の raw PD 環を δ 完全化し再び実 PD 完備化した環は完全忠実平坦。
方針：元の標準係数射の実剰余の離散・忠実平坦性を、既存の一般 δ 代数の完全忠実平坦性へ渡す。
規約：元の (p,d) 係数作用を明示する。最終候補への環比較は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完成した完全 δ 環候補への平坦性の移送。 -/
theorem perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule t)) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P G j hP
    (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
    (perfectPrismMonicPDSource_reduction_homology_isZero P hP f hf hdeg eσ)
    (perfectPrismMonicPDSource_reductionH0_faithfullyFlat P hP f hf hdeg eσ)

end Perfect
end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicPDPerfectionInputs

/-! ## 有限モニック族の既存 prism 候補の完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の既存多項式 prism 候補は、標準係数射に関して
元の (p,d) 上完全忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の具体的候補への平坦性。

## 方針

PD 先行 δ 完全化で得た平坦性を、元の係数射を保つ具体的環・加群同型で既存候補へ移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

標準係数射の toAlgebra を明示する。perfectoid 商上の p 完全忠実平坦性は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を持つ商候補へ p 完全忠実平坦性を移す。
-/

@[expose] public noncomputable section PerfectPrismMonicPrismCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "I" => Ideal.span {(p : A), d}
include hP hf hdeg eσ

/-- 概要：有限正次数モニック族の既存多項式 prism 候補は、標準係数射の作用で完全忠実平坦。
方針：PD 先行完全化の平坦性を係数射を保つ加群同型で移し、toAlgebra の作用と照合する。
規約：元の (p,d) と同じ係数射を使う。有限全列挙以外の補助仮定を残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の最終 perfectoid 商の平坦性への入力。 -/
theorem perfectPrismMonicPrism_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    letI := (φ).toAlgebra
    IsCompletelyFaithfullyFlat I T := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  have hM : IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule φ)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv I
      (monicPrismaticPDPerfectionCandidateModuleIso D d f).toLinearEquiv
      (perfectPrismMonicPDPerfection_isCompletelyFaithfullyFlat P hP f hf hdeg eσ)
  let := (φ).toAlgebra
  let e : baseChangeScalarModule φ ≃ₗ[A] T :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv I e hM

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicPrismCompletelyFlat

/-! ## 既存モニック prism 候補の標準剰余入力

## 概要

完全 prism 上の有限正次数モニック族について、既存候補の標準 (p,d) 係数拡大は高次 Tor が零で、
通常係数拡大が忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商への入力。

## 方針

一般 δ 代数の実 PD 完備化の同じ標準射の結果を、候補比較の A 線形同型で移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的係数射の計算。

## 規約

元の A 作用を持つ baseChangeScalarModule を固定し、商の基底環を取り替えない。

## 使われ方

生成元商と標準 mod p 商の実導来合成比較へ渡す。
-/

@[expose] public noncomputable section PerfectPrismMonicPrismResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun a : σ => monicRelation (f a) a)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hP hf hdeg eσ

/-- 概要：既存候補の標準係数加群は元の (p,d) 商への拡大で高次 Tor が零。
方針：PD 先行構成の標準 Tor 消滅を係数射を保つ加群同型で移す。
規約：有限正次数モニック族と完全 prism を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_torVanishing :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  exact scalarExtensionTorVanishing_of_iso q (monicPrismaticPDPerfectionCandidateModuleIso D d f)
    (perfectPrismDeltaAlgebraPD_torVanishing P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero P hP f hf hdeg eσ)
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat P hP f hf hdeg eσ))

/-- 概要：既存候補の同じ標準係数加群の通常 (p,d) 係数拡大は忠実平坦。
方針：PD 先行構成の通常剰余忠実平坦性を同じ線形比較で移す。
規約：元の係数商 A/(p,d) と実係数射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_scalarExtension_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  let M₀ : ModuleCat.{u} A := baseChangeScalarModule t
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M₀) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero P hP f hf hdeg eσ)
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat P hP f hf hdeg eσ)
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q).obj M₀)
    (((ModuleCat.extendScalars q).mapIso
      (monicPrismaticPDPerfectionCandidateModuleIso D d f)).toLinearEquiv.symm)

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicPrismResidue

/-! ## 多項式 prism 候補の実生成元商と標準 perfectoid 商

## 概要

既存多項式 prism 候補の生成元による実導来商は、標準基底射を持つ perfectoid 候補の single と同型。
BS 著者版 Remark 7.15（著者版 p.62）の商の実基底変更比較。

## 方針

元と候補の生成元の正則性から Tor 消滅を得て、通常商の標準係数作用を照合する。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる具体的係数射による計算。

## 規約

この商比較は任意多項式族に対して行い、平坦性を仮定しない。

## 使われ方

prism 側の実 (p,d) 剰余入力を、元の A/d 上の標準 mod p 商へ移す。
-/

@[expose] public noncomputable section PerfectPrismMonicQuotientReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun a : σ => monicRelation (f a) a)
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "P'" => polynomialPrism D d f hd
local notation "S" => PolynomialPerfectoidCandidate D d f hd
local notation "g" => polynomialPerfectoidCandidateBaseMap D d f hd
local notation "M" => baseChangeScalarModule φ
include hP

/-- 概要：候補の生成元の正則性は、元Aのdによるスカラー作用の正則性でもある。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_generator_smul_regular :
    letI := polynomialPrismCommRing D d f
    IsSMulRegular (ModuleCat.carrier M) d := by
  let := polynomialPrismCommRing D d f
  intro x y h
  change T at x y
  change φ d * x = φ d * y at h
  exact (P').generator_regular h

/-- 概要：元と候補の生成元が正則なので、生成元商への実係数拡大はTor非輪状。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_generator_torVanishing :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing q M := by
  let := polynomialPrismCommRing D d f
  exact scalarExtensionTorVanishing_principal_of_regular d P.generator_regular M
    (perfectPrismMonicPrism_generator_smul_regular P hP f)

/-- 概要：通常生成元商の標準係数作用を既存perfectoid候補の基底射と照合する。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
def perfectPrismMonicPrism_ordinaryQuotientIso :
    letI := polynomialPrismCommRing D d f
    (ModuleCat.extendScalars q).obj M ≅ baseChangeScalarModule g := by
  let := polynomialPrismCommRing D d f
  let := polynomialPrismCoefficientAlgebra D d f
  have hI : (J).map (algebraMap A T) = (P').ideal := by
    change (J).map φ = (P').ideal
    exact polynomialPrismCoefficientMap_ideal D d f hd
  let eR : (T ⧸ (J).map (algebraMap A T)) ≃+* S := Ideal.quotEquivOfEq hI
  let Mc : ModuleCat.{u} R := ModuleCat.of R (T ⧸ (J).map (algebraMap A T))
  let Nc : ModuleCat.{u} R := baseChangeScalarModule g
  let eA : Mc ≃ₗ[R] Nc :=
    { eR.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change eR (Ideal.Quotient.mk _ (φ a) * x) =
          eR (Ideal.Quotient.mk _ (φ a)) * eR x
        exact map_mul eR _ _ }
  exact (ModuleCat.extendScalars q).mapIso (algebraSelfRestrictionIso A T) ≪≫
    (quotientAlgebraScalarExtensionEquiv J T).toModuleIso ≪≫ eA.toModuleIso

/-- 概要：元の実生成元還元は、既存perfectoid商の同じ基底射付きsingle対象と同型。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
def perfectPrismMonicPrism_derivedQuotientIso :
    letI := polynomialPrismCommRing D d f
    (boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) := by
  let := polynomialPrismCommRing D d f
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (perfectPrismMonicPrism_generator_torVanishing P hP f) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso (perfectPrismMonicPrism_ordinaryQuotientIso P f)

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicQuotientReduction

/-! ## 有限モニック族の標準 perfectoid 候補の p 完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の既存 perfectoid 候補の標準 A/d 基底射は p 完全忠実平坦。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の有限根付き候補。

## 方針

生成元商の実還元を標準候補の single と同定し、prism 側の (p,d) 剰余の Tor 消滅と
忠実平坦性を正確な標準 mod p 商へ移す。原典の BS 著者版 Proposition 7.11 を使う経路とは異なる計算。

## 規約

モニック性と正次数、有限全列挙を明示する。任意族への最終接続は別工程。

## 使われ方

既存の根方程式と整 perfectoid 性を合わせ、有限モニック族の根付き拡大を公開する。
-/

@[expose] public noncomputable section PerfectPrismMonicPerfectoidCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (eσ : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_generator P
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q₀" => Ideal.Quotient.mk I
local notation "g" => polynomialPerfectoidCandidateBaseMap D d f hd
local notation "N" => baseChangeScalarModule g
local notation "K" => Ideal.span {(p : R)}
local notation "Qp" => R ⧸ K
local notation "qp" => Ideal.Quotient.mk K
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qp)
  (Functor.obj boundedAboveDerivedSingleFunctor N)
include hP hf hdeg eσ

/-- 概要：既存多項式 prismの同じ(p,d)実還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M
    (perfectPrismMonicPrism_torVanishing P hP f hf hdeg eσ)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

/-- 概要：同じ多項式 prismの実(p,d)還元のH0は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_pairH0_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q₀).obj M) :=
    perfectPrismMonicPrism_scalarExtension_faithfullyFlat P hP f hf hdeg eσ
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q₀).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app M).toLinearEquiv

/-- 概要：perfectoid商の標準基底射の実mod p還元の非零次数は消える。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := polynomialPrismCommRing D d f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj
      ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)).obj) := by
    let HQ (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pair_homology_isZero P hP f hf hdeg eσ i hi
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
      (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).symm

/-- 概要：同じ実mod p還元のH0は、正確な基底剰余環上で忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_modPH0_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) := by
  let := polynomialPrismCommRing D d f
  let W := (boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj) := by
    let HQ (a : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), a})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismMonicPrism_pairH0_faithfullyFlat P hP f hf hdeg eσ
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
        (perfectPrismMonicPrism_derivedQuotientIso P hP f)))).toLinearEquiv.symm

/-- 概要：同じperfectoid商の基底係数加群の高次mod p Torは零。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_torVanishing :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing qp N := by
  let := polynomialPrismCommRing D d f
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
  intro n hn
  exact (perfectPrismMonicPerfectoid_modP_homology_isZero
    P hP f hf hdeg eσ (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm

/-- 概要：同じperfectoid商の通常mod p係数拡大は忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj N) := by
  let := polynomialPrismCommRing D d f
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) :=
    perfectPrismMonicPerfectoid_modPH0_faithfullyFlat P hP f hf hdeg eσ
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm

/-- 概要：有限正次数モニック族のperfectoid候補の標準基底射はp完全忠実平坦。
方針：標準生成元商と mod p 商の実合成比較に、prism 側の実剰余入力を移す。
規約：完全 prism 上の有限正次数モニック族と同じ標準基底射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き perfectoid 候補の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    IsCompletelyFaithfullyFlat K (ModuleCat.carrier N) := by
  let := polynomialPrismCommRing D d f
  let Nc : ModuleCat.{u} R := N
  have hff : Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj Nc) :=
    perfectPrismMonicPerfectoid_scalarExtension_faithfullyFlat P hP f hf hdeg eσ
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction K Nc
    (perfectPrismMonicPerfectoid_torVanishing P hP f hf hdeg eσ) hff.1, ?_⟩
  let e := (quotientScalarExtensionEquiv K Nc).trans (quotientTensorReductionEquiv K Nc).symm
  let := hff
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：有限正次数モニック族の既存 perfectoid 候補の標準基底射は p 完全忠実平坦。
方針：制限加群の完全忠実平坦性を、同じ環射の toAlgebra の作用と恒等線形同型で照合する。
規約：基底環は元の A/d、係数射は候補構成の標準射を使う。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の有限根付き拡大。 -/
theorem perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat :
    letI := polynomialPrismCommRing D d f
    letI := (g).toAlgebra
    IsCompletelyFaithfullyFlat K (PolynomialPerfectoidCandidate D d f hd) := by
  let := polynomialPrismCommRing D d f
  have hN := perfectPrismMonicPerfectoid_isCompletelyFaithfullyFlat P hP f hf hdeg eσ
  let := (g).toAlgebra
  let e : N ≃ₗ[R] PolynomialPerfectoidCandidate D d f hd :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a y
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def] }
  exact isCompletelyFaithfullyFlat_of_linearEquiv K e hN

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicPerfectoidCompletelyFlat

/-! ## 完全 prism 商上の有限モニック族の根付き拡大

## 概要

完全 prism の商上の有限正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一段の有限版。

## 方針

同次数モニック lift を固定し、既存候補の標準基底射の完全忠実平坦性を適用する。
商の係数射で評価を移して、元の多項式族の根を得る。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる PD 先行構成と具体的比較による経路である。

## 規約

正次数を明示し、有限性は全列挙または Fintype で与える。
任意族の最終目標を宣言するものではない。

## 使われ方

一元と有限族の拡大を供給し、後の任意族への有向系の構成に使う。
-/

@[expose] public noncomputable section PerfectPrismMonicRootedExtension

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}
include hP

set_option maxHeartbeats 800000 in
-- 同じ候補の完備化台環と標準係数作用を含む存在証人の定義展開に必要。
/-- 概要：完全 prism 商上の有限正次数モニック族の全根を同じ p 完全忠実平坦拡大に得る。
方針：同次数モニック lift に候補の平坦性を適用し、評価の自然性で根を降ろす。
規約：有限全列挙以外に補助的な平坦性仮定は要求しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の別証明の有限段。 -/
theorem exists_finiteMonicRootedPerfectoidExtension_of_perfectPrism
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let F := perfectPrismMonicLift P f hf
  have hF : ∀ s, (F s).Monic := fun s => (perfectPrismMonicLift_spec P f hf s).2
  have hFdeg : ∀ s, 0 < (F s).natDegree := by
    intro s
    rw [(perfectPrismMonicLift_spec P f hf s).1]
    exact hdeg s
  let D := P.deltaStructure
  let d := P.generator
  let hd := OrientedPrism.isDistinguished_generator P
  let := polynomialPrismCommRing D d F
  let φ := polynomialPerfectoidCandidateBaseMap D d F hd
  let ρ := polynomialPerfectoidCandidateRoot D d F hd
  refine ⟨PolynomialPerfectoidCandidate D d F hd, inferInstance, φ, ρ,
    polynomialPerfectoidCandidate_isIntegralPerfectoid D d F hd,
    perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat P hP F hF hFdeg eσ, ?_⟩
  intro s
  rw [← perfectPrismMonicLift_map P f hf s, Polynomial.eval₂_map]
  exact polynomialPerfectoidCandidate_eval D d F hd s

/-- 概要：Fintype で与えた有限正次数モニック族にも同じ根付き拡大が存在する。
方針：Fin からの全列挙を選び、有限族の存在定理を適用する。
規約：根の型は元の添字型のままに保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の任意有限部分族への適用。 -/
theorem exists_monicRootedPerfectoidExtension_of_perfectPrism_fintype [Fintype σ]
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 :=
  exists_finiteMonicRootedPerfectoidExtension_of_perfectPrism P hP f hf hdeg
    (Fintype.equivFin σ).symm

/-- 概要：完全 prism 商上の一つの正次数モニック多項式に根を持つ p 完全忠実平坦拡大がある。
方針：一元添字族に有限族の存在定理を適用する。
規約：次数は正とするが、多項式の形に追加の制限を課さない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の一元の根添加。 -/
theorem exists_monicRootPerfectoidExtension_of_perfectPrism
    (f : Polynomial R) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      f.eval₂ φ ρ = 0 := by
  obtain ⟨T, hT, φ, ρ, hperf, hflat, hroot⟩ :=
    exists_monicRootedPerfectoidExtension_of_perfectPrism_fintype P hP
      (fun _ : PUnit.{u + 1} => f) (fun _ => hf) (fun _ => hdeg)
  exact ⟨T, hT, φ, ρ PUnit.unit, hperf, hflat, hroot PUnit.unit⟩

end SerrePositivity.BhattScholze.Andre

end PerfectPrismMonicRootedExtension
