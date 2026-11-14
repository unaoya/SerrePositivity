module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.AdicCompletion.Topology
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection

/-!
# perfectoid 環と完全 prism（BS 著者版 Theorem 3.10）

## 概要
完全 prism の商は perfectoid、perfectoid 環の Fontaine 核は distinguished 元で生成され、W(R♭) の導来 (p,d) 完備化の商として表せる。
Fontaine 写像の自然性、環同型による perfectoid 性の移送、完全 prism の Witt 表示。
完全 prism の台環を Witt 環から復元する補助には、BS 著者版 Corollary 2.31 を使う。

## 方針
完全 prism を Witt 環で表し、Witt 商の計算に帰着する。

## 規約
圏同値ではなく三つの事実（商の perfectoid 性、perfectoid 環の prism 表示、射の持ち上げ）として述べる（BS 著者版 Theorem 3.10 の構成部分）。

## 使われ方
BS 著者版 Corollary 7.3、André、perfectoid 環のテンソル（Perfectoidization）、CLMST。
-/

universe u

/-! ## BSの完全prism対応に使うFontaine写像の自然性

共通Witt持上げの一意性から導く。環のp正則性は要求しない。
-/

@[expose] public noncomputable section FontaineNaturality

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 任意のp進完備環の射は、標準tilt射を介してFontaine写像と可換する。 -/
theorem fontaineTheta_natural (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp
      (WittVector.map (Perfection.map p (modPMap p f))) =
      f.comp (WittVector.fontaineTheta R p) := by
  apply wittLift_unique
  apply RingHom.ext
  intro x
  change Ideal.Quotient.mk _ (WittVector.fontaineTheta S p
    (WittVector.map (Perfection.map p (modPMap p f)) x)) =
    Ideal.Quotient.mk _ (f (WittVector.fontaineTheta R p x))
  rw [WittVector.mk_fontaineTheta, WittVector.map_coeff]
  change modPMap p f (PreTilt.coeff 0 (x.coeff 0)) = _
  rw [← WittVector.mk_fontaineTheta]
  rfl

end SerrePositivity.BhattScholze

end FontaineNaturality

/-! ## Fontaine核のdistinguished生成元の底変換

既存の核判定と自然性を使い、源の生成元の像が終域の核を生成することを示す。
環そのもののp正則性を要求しない。
-/

@[expose] public noncomputable section FontaineKernelNaturality

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- Fontaine核内のdistinguished元の標準Witt像は、単項な終域のFontaine核を生成する。 -/
theorem fontaineKernel_eq_span_image_distinguished
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {WittVector.map (Perfection.map p (modPMap p f)) d} := by
  let m : WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) :=
    WittVector.map (Perfection.map p (modPMap p f))
  have hdist := (wittDeltaStructure_map_isDeltaHom p (PreTilt R p)
    (Perfection.map p (modPMap p f))).map_isDistinguished hd
  have hunit : IsUnit ((m d).coeff 1) :=
    (wittDeltaStructure_isDistinguished_iff p (PreTilt S p) (m d)).mp hdist
  apply PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_firstCoeff_unit
    S p hker (m d)
  · have he := RingHom.congr_fun (fontaineTheta_natural p f) d
    change WittVector.fontaineTheta S p (m d) = f (WittVector.fontaineTheta R p d) at he
    rw [hzero, map_zero] at he
    exact he
  · exact hunit.map (PreTilt.coeff 0)

end SerrePositivity.BhattScholze

end FontaineKernelNaturality

/-! ## perfectoid環のFontaine核のdistinguished生成元

既存のFontaine核判定を再利用する。pねじれを持つperfectoid環も含む。
-/

@[expose] public noncomputable section PerfectoidDistinguishedKernel

open SerrePositivity.PerfectoidFrobeniusCriterion
namespace SerrePositivity.BhattScholze
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- perfectoidの四条件から、標準Witt δ構造でdistinguishedなFontaine核生成元を得る。 -/
theorem exists_distinguished_fontaine_kernel_generator
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hpEq : (p : S) = u * π ^ p) :
    ∃ d : WittVector p (PreTilt S p),
      (wittDeltaStructure p (PreTilt S p)).IsDistinguished d ∧
      RingHom.ker (WittVector.fontaineTheta S p) = Ideal.span {d} := by
  obtain ⟨q, v, a, hq, _, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hpEq
  let d : WittVector p (PreTilt S p) := (p : WittVector p (PreTilt S p)) +
    WittVector.teichmuller p q ^ p * a
  refine ⟨d, ?_, hgen⟩
  apply (wittDeltaStructure_isDistinguished_iff p (PreTilt S p) d).mpr
  apply perfection_isUnit_of_coeff_zero (ModP S p) p
  change IsUnit (PreTilt.coeff 0 (d.coeff 1))
  have hπ : π ^ p ∈ Ideal.span {(p : S)} := by
    have hh : (u : S) * π ^ p ∈ Ideal.span {(p : S)} := by
      rw [← hpEq]
      exact Ideal.mem_span_singleton_self _
    simpa [mul_assoc] using (Ideal.span {(p : S)}).mul_mem_left (↑(u⁻¹) : S) hh
  have hqpow : q.untilt ^ p ∈ Ideal.span {(p : S)} := by
    rw [hq, mul_pow]
    exact (Ideal.span {(p : S)}).mul_mem_left _ hπ
  rw [primitive_shape_firstCoeff_eq_one S p q a
    (coeff_zero_pow_eq_zero_of_untilt_pow_mem_p S p q hqpow)]
  exact isUnit_one

end SerrePositivity.BhattScholze

end PerfectoidDistinguishedKernel

/-! ## 完全prismの商同型に沿う既存perfectoid述語の移送 -/

@[expose] public noncomputable section PerfectoidRingEquiv

namespace SerrePositivity.BhattScholze
variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

private def modPEquiv (e : R ≃+* S) : ModP R p ≃+* ModP S p :=
  Ideal.quotientEquiv _ _ e (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])

omit [Fact p.Prime] in
private theorem modPEquiv_apply (e : R ≃+* S) (x : ModP R p) :
    modPEquiv p e x = modPMap p e.toRingHom x := rfl

/-- BSの商比較に使う環同型に沿って、既存の整perfectoid性を移す。 -/
theorem isIntegralPerfectoid_of_ringEquiv (e : R ≃+* S) (hR : IsIntegralPerfectoid R p) :
    IsIntegralPerfectoid S p := by
  rcases hR with hs | ⟨hp, hc, ⟨π, a, ha⟩, hF, hker⟩
  · exact Or.inl (Function.Injective.subsingleton e.symm.injective)
  · have hpS : ¬ IsUnit (p : S) := by
      intro hu
      apply hp
      simpa only [map_natCast] using hu.map e.symm.toRingHom
    have hcS : IsAdicComplete (Ideal.span {(p : S)}) S := by
      have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {(p : R)}) e).mpr hc
      simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
    let := hc
    let := hcS
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    let : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
    let em := modPEquiv p e
    let t := Perfection.map p (modPMap p e.toRingHom)
    have ht : Function.Bijective t := by
      constructor
      · intro x y h
        apply Perfection.ext
        intro n
        apply em.injective
        have hh := congrArg (Perfection.coeff (ModP S p) p n) h
        change modPMap p e.toRingHom (Perfection.coeff (ModP R p) p n x) =
          modPMap p e.toRingHom (Perfection.coeff (ModP R p) p n y) at hh
        exact hh
      · intro y
        refine ⟨Perfection.map p em.symm.toRingHom y, ?_⟩
        apply Perfection.ext
        intro n
        change em (em.symm (Perfection.coeff (ModP S p) p n y)) = _
        exact em.apply_symm_apply _
    let ψ : WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) := WittVector.map t
    have hψ : Function.Surjective ψ := WittVector.map_surjective _ ht.2
    refine Or.inr ⟨hpS, hcS, ⟨e π, Units.map e.toMonoidHom a, ?_⟩, ?_, ?_⟩
    · change (p : S) = e (a : R) * (e π) ^ p
      simpa only [map_natCast, map_mul, map_pow] using congrArg e ha
    · intro y
      obtain ⟨x, hx⟩ := hF (em.symm y)
      refine ⟨em x, ?_⟩
      change (em x) ^ p = y
      change x ^ p = em.symm y at hx
      rw [← map_pow, hx, em.apply_symm_apply]
    · have he : (RingHom.ker (WittVector.fontaineTheta S p)).comap ψ =
          RingHom.ker (WittVector.fontaineTheta R p) := by
        ext x
        change WittVector.fontaineTheta S p (ψ x) = 0 ↔
          WittVector.fontaineTheta R p x = 0
        have hn := RingHom.congr_fun (fontaineTheta_natural p e.toRingHom) x
        change WittVector.fontaineTheta S p (ψ x) = e (WittVector.fontaineTheta R p x) at hn
        rw [hn, map_eq_zero_iff e e.injective]
      have hm := hker.map_ringHom ψ
      rw [← he, Ideal.map_comap_of_surjective ψ hψ] at hm
      exact hm

end SerrePositivity.BhattScholze

end PerfectoidRingEquiv

/-! ## 完全oriented prismの標準Witt表示

既存のWitt復元同型と選択生成元をそのまま使い、主イデアルと標準商を比較する。
環・商の比較は零環を含む。標準Witt δ構造との両立にはmod p環のCharPを明示する。
-/

@[expose] public noncomputable section PerfectPrismWittPresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)

/-- 完全prismのp完備性を供給した、既存のWitt復元同型そのもの。 -/
abbrev perfectPrismWittRecoveryEquiv : WittVector p (ModP A p) ≃+* A :=
  letI := P.isAdicComplete_p_of_perfect hP
  perfectDeltaWittRecoveryEquiv P.deltaStructure hP

/-- 同じ復元同型の逆像として定める、選択済みprism生成元のWitt表示。 -/
abbrev perfectPrismWittGenerator : WittVector p (ModP A p) :=
  (perfectPrismWittRecoveryEquiv P hP).symm P.generator

/-- Witt表示の生成元は、元の選択生成元へ写る。 -/
@[simp] theorem perfectPrismWittRecoveryEquiv_generator :
    perfectPrismWittRecoveryEquiv P hP (perfectPrismWittGenerator P hP) = P.generator :=
  (perfectPrismWittRecoveryEquiv P hP).apply_symm_apply _

/-- Witt生成元の主イデアルの像は、元のprismイデアル。 -/
theorem perfectPrismWittGenerator_map_span :
    (Ideal.span {perfectPrismWittGenerator P hP}).map
      (perfectPrismWittRecoveryEquiv P hP).toRingHom = P.ideal := by
  simp only [Ideal.map_span, Set.image_singleton]
  change Ideal.span {perfectPrismWittRecoveryEquiv P hP (perfectPrismWittGenerator P hP)} =
    Ideal.span {P.generator}
  rw [perfectPrismWittRecoveryEquiv_generator]

/-- 逆方向にも、元のprismイデアルは同じWitt生成元の主イデアルへ写る。 -/
theorem perfectPrismWittRecoveryEquiv_symm_map_ideal :
    P.ideal.map (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom =
      Ideal.span {perfectPrismWittGenerator P hP} := by
  simp only [OrientedPrism.ideal, Ideal.map_span, Set.image_singleton]
  rfl

/-- 同じWitt環は、復元した生成元について古典的完備。 -/
theorem perfectPrismWitt_isAdicComplete_generator :
    IsAdicComplete (Ideal.span {perfectPrismWittGenerator P hP}) (WittVector p (ModP A p)) := by
  have h := (IsAdicComplete.congr_ringEquiv P.ideal
    (perfectPrismWittRecoveryEquiv P hP).symm).mpr P.isAdicComplete_generator
  change IsAdicComplete
    (P.ideal.map (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom) (WittVector p (ModP A p)) at h
  simpa only [perfectPrismWittRecoveryEquiv_symm_map_ideal] using h

/-- 同じ復元環同型から誘導される、Witt主イデアル商と元のprism商の比較。 -/
def perfectPrismWittQuotientEquiv :
    WittVector p (ModP A p) ⧸ Ideal.span {perfectPrismWittGenerator P hP} ≃+* A ⧸ P.ideal :=
  Ideal.quotientEquiv _ _ (perfectPrismWittRecoveryEquiv P hP)
    (perfectPrismWittGenerator_map_span P hP).symm

/-- 商比較は元のWitt元の標準商像を保つ。 -/
@[simp] theorem perfectPrismWittQuotientEquiv_mk (x : WittVector p (ModP A p)) :
    perfectPrismWittQuotientEquiv P hP (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk P.ideal (perfectPrismWittRecoveryEquiv P hP x) := rfl

/-- 商比較の逆射も、元の環の標準商像に関する公式を持つ。 -/
@[simp] theorem perfectPrismWittQuotientEquiv_symm_mk (a : A) :
    (perfectPrismWittQuotientEquiv P hP).symm (Ideal.Quotient.mk P.ideal a) =
      Ideal.Quotient.mk _ ((perfectPrismWittRecoveryEquiv P hP).symm a) := rfl

section DeltaCompatibility
variable [CharP (ModP A p) p]

/-- mod p環が標数pを持つ場合、同じ復元同型は標準Witt δ構造と両立する。 -/
theorem perfectPrismWittRecoveryEquiv_isDeltaHom :
    letI := hP.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDeltaHom P.deltaStructure
      (perfectPrismWittRecoveryEquiv P hP).toRingHom := by
  let := hP.perfectRing_mod_p
  let := P.isAdicComplete_p_of_perfect hP
  exact perfectDeltaWittRecoveryEquiv_isDeltaHom P.deltaStructure hP

/-- 逆方向の復元同型も同じ標準Witt δ構造と両立する。 -/
theorem perfectPrismWittRecoveryEquiv_symm_isDeltaHom :
    letI := hP.perfectRing_mod_p
    P.deltaStructure.IsDeltaHom (wittDeltaStructure p (ModP A p))
      (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom := by
  let := hP.perfectRing_mod_p
  let := P.isAdicComplete_p_of_perfect hP
  exact perfectDeltaWittRecoveryEquiv_symm_isDeltaHom P.deltaStructure hP

/-- 選択生成元のWitt表示は、標準Witt δ構造についてdistinguished。 -/
theorem perfectPrismWittGenerator_isDistinguished :
    letI := hP.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDistinguished (perfectPrismWittGenerator P hP) := by
  let := hP.perfectRing_mod_p
  exact (perfectPrismWittRecoveryEquiv_symm_isDeltaHom P hP).map_isDistinguished
    (P.isDistinguished_generator)

end DeltaCompatibility
end SerrePositivity.BhattScholze

end PerfectPrismWittPresentation

/-! ## 一般の完全oriented prismの商のperfectoid性

BS 著者版 Theorem 3.10の商の向き。商のpねじれを許し、F7を要求しない。
-/

@[expose] public noncomputable section PerfectPrismQuotientPerfectoid

namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 向き付き完全 prism の標準商は整 perfectoid（BS 著者版 Theorem 3.10 の商を取る方向、序論の Example 1.3 (2)）。
  零環も含む。 -/
theorem quotient_isIntegralPerfectoid (P : OrientedPrism p A)
    (hP : P.deltaStructure.IsPerfect) : IsIntegralPerfectoid (A ⧸ P.ideal) p := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · let := hs
    exact Or.inl inferInstance
  · let := hn
    let := P.isAdicComplete_p_of_perfect hP
    have hp : ¬ IsUnit (p : A) := by
      intro hu
      let : Subsingleton A := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
      exact zero_ne_one (Subsingleton.elim (0 : A) 1)
    let : Fact (¬ IsUnit (p : A)) := ⟨hp⟩
    let := hP.perfectRing_mod_p
    let k := ModP A p
    let d := perfectPrismWittGenerator P hP
    have hd : (wittDeltaStructure p k).IsDistinguished d :=
      perfectPrismWittGenerator_isDistinguished P hP
    let : IsAdicComplete (Ideal.span {d}) (WittVector p k) :=
      perfectPrismWitt_isAdicComplete_generator P hP
    let eq : WittVector p k ⧸ Ideal.span {d} ≃+* A ⧸ P.ideal :=
      perfectPrismWittQuotientEquiv P hP
    exact isIntegralPerfectoid_of_ringEquiv p eq
      (wittCompleteDistinguishedQuotient_isIntegralPerfectoid p k d hd)

end SerrePositivity.BhattScholze.OrientedPrism

end PerfectPrismQuotientPerfectoid

/-! ## 任意の非零perfectoid試験環の完全prism商表示

標準Fontaine核を実PD完備化し、実H⁰の商比較で試験環を復元する。
Fontaine核進完備性や試験環のp正則性を仮定しない。
-/

@[expose] public noncomputable section PerfectoidTrialPrism

namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (T : Type u) [CommRing T] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : T))] [IsAdicComplete (Ideal.span {(p : T)}) T]

/-- 整 perfectoid 環の四条件の非零枝から、完全 prism と試験環への商同型を得る
（BS 著者版 Theorem 3.10 の perfectoid 環から完全 prism を作る方向の非零枝）。 -/
theorem exists_perfectoidTrialPrism
    (hF : Function.Surjective (fun x : ModP T p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta T p)).IsPrincipal)
    (π : T) (u : Tˣ) (hpEq : (p : T) = u * π ^ p) :
    ∃ (d : WittVector p (PreTilt T p))
      (hd : (wittDeltaStructure p (PreTilt T p)).IsDistinguished d),
      letI := pdCompletionCommRing (WittVector p (PreTilt T p)) p d
      ∃ e : PDCompletionH0 (WittVector p (PreTilt T p)) p d ⧸
          (perfectDeltaPDPrism (wittDeltaStructure p (PreTilt T p))
            (wittDeltaStructure_isPerfect p (PreTilt T p)) d hd).ideal ≃+* T,
        e.toRingHom.comp ((Ideal.Quotient.mk _).comp
          (pdCompletionUnit (WittVector p (PreTilt T p)) p d)) =
          WittVector.fontaineTheta T p := by
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator T p hF hker π u hpEq
  refine ⟨d, hd, ?_⟩
  let := pdCompletionCommRing (WittVector p (PreTilt T p)) p d
  exact exists_perfectDeltaPDQuotientEquiv (wittDeltaStructure p (PreTilt T p))
    (wittDeltaStructure_isPerfect p (PreTilt T p)) d hd (WittVector.fontaineTheta T p)
    (fun x ↦ surjective_fontaineTheta hF x) hk

end SerrePositivity.BhattScholze

end PerfectoidTrialPrism

/-! ## distinguished Witt商のperfectoid性の一般入口

実PD完備化後の商とp完備な標準商の比較を使い、Witt環のd完備性の仮定を除く。
標準Fontaine比較射自体の同型とは区別する。
-/

@[expose] public noncomputable section WittDistinguishedQuotientPerfectoid

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 完全係数環の任意のdistinguished Witt商はperfectoid（BS 著者版 Theorem 3.10 の完全 Witt 環からの商の方向）。
台Witt環のd完備性、商のp正則性・非零性を要求しない。 -/
theorem wittDistinguishedQuotient_isIntegralPerfectoid
    (d : WittVector p k) (hd : (wittDeltaStructure p k).IsDistinguished d) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p := by
  let D := wittDeltaStructure p k
  have hD := wittDeltaStructure_isPerfect p k
  let T := WittVector p k ⧸ Ideal.span {d}
  let q := Ideal.Quotient.mk (Ideal.span {d})
  let := hD.distinguished_quotient_isAdicComplete hd
  let := pdCompletionCommRing (WittVector p k) p d
  obtain ⟨e, _⟩ := exists_perfectDeltaPDQuotientEquiv D hD d hd q
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h := (perfectDeltaPDPrism D hD d hd).quotient_isIntegralPerfectoid
    (perfectDeltaPDPrism_isPerfect D hD d hd)
  exact isIntegralPerfectoid_of_ringEquiv p e h

end SerrePositivity.BhattScholze

end WittDistinguishedQuotientPerfectoid

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 1.3" (partial := special) "(1) 結晶 prism は本体（OrientedPrism.crystalline）。(2) 完全 prism ↔ perfectoid は Thm 3.10 の両向きを対象ごとに（圏同値としてではない）。Breuil–Kisin・q 型などの他の例は不要 ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：perfectPrismWittRecoveryEquiv（W(A/p) ≃ A を与える。R からの逆方向ではないので Example 1.3 (2) の候補から外す。Corol） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid
attribute [cite BS19 "Thm 3.10" (partial := special) "圏同値ではなく三つの事実（商の perfectoid 性・perfectoid 環の prism 表示・射の持ち上げ）で（D8）。絶対の圏同値は本体にも drafts にもない（drafts/A5 の perfectSiteEquivPerfectoidUnder は固定基底の上の相対版、Lemma 4.8 の系） ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.OrientedPrism.quotient_isIntegralPerfectoid
attribute [cite BS19 "Thm 3.10" (partial := special) "圏同値ではなく三つの事実（商の perfectoid 性・perfectoid 環の prism 表示・射の持ち上げ）で（D8）。絶対の圏同値は本体にも drafts にもない（drafts/A5 の perfectSiteEquivPerfectoidUnder は固定基底の上の相対版、Lemma 4.8 の系） ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.exists_perfectoidTrialPrism
attribute [cite BS19 "Thm 3.10" (partial := special) "圏同値ではなく三つの事実（商の perfectoid 性・perfectoid 環の prism 表示・射の持ち上げ）で（D8）。絶対の圏同値は本体にも drafts にもない（drafts/A5 の perfectSiteEquivPerfectoidUnder は固定基底の上の相対版、Lemma 4.8 の系） ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.wittDistinguishedQuotient_isIntegralPerfectoid
