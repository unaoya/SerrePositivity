module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.FiniteProduct
public import SerrePositivity.BhattScholze.Perfectoidization.ExcisionTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompleteCommonModel
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Tor
public import SerrePositivity.BhattScholze.Andre.TorDescent
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import SerrePositivity.CommutativeAlgebra.DerivedSingleTrianglePullback

/-! # 有限比較の excision と perfectoid イデアルの Tor の入力

## 概要

KL の標準 excision の四角（`KLCanonicalExcisionSquare`）と、有限比較がそれを満たすという述語 `KLFiniteComparisonExcision` を定める。絶対整閉な被覆の上でこの述語が成り立てば perfectoid イデアルの冪ねじれ Tor の入力が得られること、André 拡大の上でそれを示せば十分であること（`exists_andre_extension_finiteComparison_excision_suffices`）を与える。perfectoid な基底の上の有限比較がこの述語を満たすことを証明する（`klFiniteComparisonExcision_of_perfectoid`）。

## 方針

有限表示性から導来 p 完備性を、核・余核の台の条件から主局所化の全単射性を得て、整写像の標準 excision（BS 著者版 Corollary 8.12 の環版の系、`Perfectoidization/Excision`）へ渡す。André 拡大は試験加群・指数・次数より前に一つ選ぶ。

## 規約

旧 `CLMST/KLAicTorFromExcision`・`KLOriginalTorFromExcision` と、`CLMST/KLFiniteComparisonExcision` の証明の部分。主張 Prop 2.4.9(a)（`perfectoidIdeal_powerTorsionTorInput`）は CLMST/KoszulAnnihilation に残る。比較写像の Tor 消滅を CLMST の Prop 2.4.7 と Prop 2.4.9(a) へ渡す。

## 使われ方

CLMST の Prop 2.4.7・Prop 2.4.9(a)・Thm 4.0.3。
-/

@[expose] public noncomputable section

universe u

section KLAicTorFromExcisionPart

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.BhattScholze
set_option backward.isDefEq.respectTransparency false

/-- The exact canonical excision square for the specified original units. -/
abbrev KLCanonicalExcisionSquare
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R) : Prop :=
  IsPullback
    (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
    (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf
      (Ideal.span {algebraMap R A a})))
    (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
    (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})))

/-- Unproved excision input needed by KL, with the actual finite presentation
sources, finite map and supported errors. Completeness and localization data
for the applications have already been proved; the pullback assertion has not. -/
def KLFiniteComparisonExcision (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    (a : R) (q : A →ₐ[R] B) (_hq : q.toRingHom.Finite)
    (_hk : ∀ x, q x = 0 → ∃ n : ℕ, a ^ n • x = 0)
    (_hc : ∃ n : ℕ, ∀ y : B ⧸ q.toLinearMap.range, a ^ n • y = 0)
    (f : A →ₐ[R] C) (g : B →ₐ[R] D)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom),
    KLCanonicalExcisionSquare hf hg q a

/-- On the AIC base, the sole missing finite-comparison excision assertion
supplies the full original ideal Tor input. Every local model and universal
unit is fixed before all power-torsion tests. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (hExcision : KLFiniteComparisonExcision R p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨t, ht, _hpow, hmodels⟩ :=
    aic_finiteEtaleAway_exists_derivedComplete_common_cover p hR hAIC a hetale
  apply BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover R p hR hAIC a t ht C
  intro z
  obtain ⟨r, _e, M, hM, aM, hfinite, hfp, _hmfp, _hcR, _hcM, _hcI, _hcQ,
    u, v, _w, _hu, _hv, _hloc, huF, hvF, _htu, _htv, huk, hvk, n, huc, hvc⟩ :=
    hmodels z.1 z.2
  let : Module.Finite R M := hfinite
  let : Algebra.FinitePresentation R M := hfp
  obtain ⟨D, hD, g₀, hg₀⟩ := Inputs.exists_perfectoidization_of_integral R M p hR
  let := hD
  let : Algebra R D := (g₀.comp (algebraMap R M)).toAlgebra
  let g : M →ₐ[R] D := { g₀ with commutes' := fun _ => rfl }
  have hg : IsPerfectoidization p g.toRingHom := hg₀
  let h : (Fin r → R) →ₐ[R] (Fin r → R) := AlgHom.id R _
  have hh : IsPerfectoidization p h.toRingHom :=
    (isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id
  exact BhattScholze.perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision p hR
    (a * (IsLocalization.Away.sec a z.1).1) r u v f g h hf hg hh
    (hExcision A M C D _ u huF huk ⟨n, huc⟩ f g hf hg)
    (hExcision (Fin r → R) M (Fin r → R) D _ v hvF hvk ⟨n, hvc⟩ h g hh hg)

end SerrePositivity.BhattScholze

end KLAicTorFromExcisionPart

section KLOriginalTorFromExcisionPart

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- One Andre extension is selected before all finite presentation algebras,
generators, universal targets and tests. Excision on this same extension then
supplies the original full ideal Tor input for every algebra etale off a. -/
theorem exists_andre_extension_finiteComparison_excision_suffices
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      ∃ _hE : IsIntegralPerfectoid E p,
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      (KLFiniteComparisonExcision E p →
        ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
          [Module.Finite R A] [Algebra.FinitePresentation R A]
          (a : R) (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom),
          letI := GenericEtale.awayAlgebra R A a
          Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
            ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
              ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
                torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, hdesc⟩ :=
    BhattScholze.exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput R p hR
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro hExcision A C _ _ _ _ _ _ a f hf
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨D, hD, g₀, hg₀⟩ :=
    BhattScholze.Inputs.exists_perfectoidization_of_integral E (E ⊗[R] A) p hE
  let := hD
  let : Algebra E D := (g₀.comp (algebraMap E (E ⊗[R] A))).toAlgebra
  let g : E ⊗[R] A →ₐ[E] D := { g₀ with commutes' := fun _ => rfl }
  have hg : IsPerfectoidization p g.toRingHom := hg₀
  have he := etaleAway_tensor_baseChange (B := E) a hetale
  let := GenericEtale.awayAlgebra E (E ⊗[R] A) (algebraMap R E a)
  have hTor := perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
    p hE haic hExcision (algebraMap R E a) g hg he
  exact hdesc A C f hf D g hg a hTor

/-- The original full Tor statement follows once the explicit finite-comparison
excision input is supplied on AIC perfectoid extensions of the original base.
This theorem remains conditional on that input. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (E : Type u) [CommRing E] [Algebra R E],
      IsIntegralPerfectoid E p → IsAbsolutelyIntegrallyClosed E → KLFiniteComparisonExcision E p)
    (a : R) (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    letI := GenericEtale.awayAlgebra R A a
    Algebra.Etale (Localization.Away a) (Localization.Away (algebraMap R A a)) →
      ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
        ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
          torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let := GenericEtale.awayAlgebra R A a
  intro hetale
  obtain ⟨E, hEring, hEalg, hE, _hflat, haic, _ρ, _hρ0, _hρ, hTor⟩ :=
    exists_andre_extension_finiteComparison_excision_suffices R p hR
  exact hTor (hExcision E hE haic) A C a f hf hetale

end SerrePositivity.BhattScholze

end KLOriginalTorFromExcisionPart

section PerfectoidFiniteComparisonExcisionPart

namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false

/--
## 概要
perfectoid 基底上の有限比較は KLFiniteComparisonExcision を満たす。

## 方針
元の有限性・有限表示性から始域・終域と主イデアルの導来完備性を供給する。
核・余核の支持条件で元の主局所化写像を全単射にし、整写像の標準 excision 定理を使う。

## 使われ方
共通モデルへの二写像の hPBu、hPBv を解消し、Prop 2.4.9(a) と KL-Q へ渡す。
-/
theorem klFiniteComparisonExcision_of_perfectoid
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : KLFiniteComparisonExcision R p := by
  intro A B C D _ _ _ _ _ _ _ _ _ _ _ _ a q hq hk hc f g hf hg
  let : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  let : Module.FinitePresentation R B :=
    Module.FinitePresentation.of_finite_of_finitePresentation R B
  have hA := isModuleComplete_finitePresentation_algebra_principal R A
    (p : R) (algebraMap R A a) (hR.isModuleComplete R p)
  have hB := isModuleComplete_finitePresentation_algebra_principal R B
    (p : R) (algebraMap R B a) (hR.isModuleComplete R p)
  simp only [map_natCast] at hA hB
  let : Algebra A B := q.toRingHom.toAlgebra
  let : Module.Finite A B := hq
  obtain ⟨n, hn⟩ := hc
  have haway := localizationComparison_awayMap_bijective_of_power_bounds a q hk (by
    intro y
    refine ⟨n, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero q.toLinearMap.range).mp
    change q.toLinearMap.range.mkQ (a ^ n • y) = 0
    exact (q.toLinearMap.range.mkQ.map_smul (a ^ n) y).trans (hn _))
  exact klCanonicalExcisionSquare_of_integral_away R p hR A B C D q a f g hf hg
    hA.2.1 hB.2.1 hA.2.2.1 haway

end SerrePositivity.BhattScholze

end PerfectoidFiniteComparisonExcisionPart

section CanonicalSingleTriangleBridgePart

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated _root_.SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The integer-module product/difference complex of the original canonical
excision square, using precisely its original four ring homomorphisms. -/
def canonicalExcisionIntegerModuleComplex
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R) : ShortComplex (ModuleCat.{u} ℤ) :=
  ringHomPullbackShortComplex (IsPerfectoidization.map hf hg q.toRingHom)
    (perfectoidizationClosedSideProjection hf (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom))
    (perfectoidizationClosedComparison hf hg q.toRingHom (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedComparison_square hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})).symm

/-- The actual distinguished triangle on the specified integer-module single
objects supplies exactly the missing canonical ring pullback assertion. -/
theorem canonicalExcision_isPullback_of_distinguished_single_triangle
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R)
    (δ : (DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj
        (canonicalExcisionIntegerModuleComplex hf hg q a).X₃ ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).obj
        (canonicalExcisionIntegerModuleComplex hf hg q a).X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (canonicalExcisionIntegerModuleComplex hf hg q a).f)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} ℤ) 0).map
        (canonicalExcisionIntegerModuleComplex hf hg q a).g) δ ∈ distTriang _) :
    BhattScholze.KLCanonicalExcisionSquare hf hg q a :=
  ringHom_isPullback_of_distinguished_single_triangle
    (IsPerfectoidization.map hf hg q.toRingHom)
    (perfectoidizationClosedSideProjection hf (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedSideProjection hg
      ((Ideal.span {algebraMap R A a}).map q.toRingHom))
    (perfectoidizationClosedComparison hf hg q.toRingHom (Ideal.span {algebraMap R A a}))
    (perfectoidizationClosedComparison_square hf hg q.toRingHom
      (Ideal.span {algebraMap R A a})).symm δ hT

end SerrePositivity.BhattScholze

end CanonicalSingleTriangleBridgePart
