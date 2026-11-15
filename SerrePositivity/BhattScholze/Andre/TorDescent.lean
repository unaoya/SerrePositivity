module

public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.TorCoefficientPowerTorsionDescent
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Tor
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator

/-! # André 拡大による冪ねじれ Tor の検出と降下

## 概要

BS 著者版 Theorem 7.14 の André 拡大を一つ選ぶと、元の冪ねじれ加群の Tor の係数への作用（完備な基底変更の Tor を含む）がその拡大の後で検出できること、perfectoid 化を基底変更した後の Tor も同じ拡大で検出できることを示す。これにより、perfectoid イデアルの冪ねじれ Tor の入力を André 拡大から元の環へ降ろす（`exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput`）。元の `baseChangeScalarModule` に対する p 完全忠実平坦な降下の基底も与える（`exists_andre_descent_base`）。

## 方針

拡大は `R` から一度だけ選び、代数・生成元・perfectoid 化の模型・検査のどれにも依存させない。

## 規約

使う深い入力は BS 著者版 Theorem 7.14 の拡大だけで、絶対整閉化の分裂や perfectoid の基底変更の比較は主張しない。旧 `CLMST/AndreTorDescent`・`AndrePerfectoidizationTorDescent`・`AndrePerfectoidIdealTorDescent`・`Prop247AndreBase`（`prop247_` を外した）。

## 使われ方

CLMST の KL 比較（Thm 4.0.3）と Prop 2.4.7 の一般階数の降下。
-/

@[expose] public noncomputable section

universe u

section AndreTorDescentPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard

/-- Choose the actual André extension once for the base ring, independently of every Tor test.
Only the existing BS 著者版 Theorem 7.14 citation is used to supply this extension. -/
lemma exists_andre_extension_detects_powerTorsion_Tor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧
      (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C]
        (N : ModuleCat.{u} R) (k : ℕ) (_hN : ∀ x : N, (p : R) ^ k • x = 0)
        (i : ℕ) (s : R),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
          ∀ x : (DerivedCategory.homologyFunctor (ModuleCat E) (-(i : ℤ))).obj
            ((boundedAboveDerivedBaseChange (algebraMap R E)).obj
              (boundedAboveDerivedTensor.obj
                (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C),
                  boundedAboveDerivedSingleFunctor.obj N))).obj,
            algebraMap R E s • x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic⟩ :=
    BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  letI := hEring
  letI := hEalg
  let e : baseChangeScalarModule (algebraMap R E) ≅ ModuleCat.of R E :=
    algebraSelfRestrictionIso R E
  have hφ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)}) e.toLinearEquiv.symm hflat
  have hroots : ∀ s : E, ∃ ρ : ℕ → E,
      ρ 0 = s ∧ ∀ n, ρ (n + 1) ^ p = ρ n :=
    fun s => haic.exists_compatible_pow_roots (Fact.out : p.Prime).pos s
  choose ρ hρ0 hρ using hroots
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro C _ _ N k hN i s
  exact torCoefficientScalar_eq_zero_iff_powerTorsion_baseChange
    (algebraMap R E) (p : R) hφ N k hN i s

/-- One actual André extension detects all original Tor tests on every perfectoid coefficient
using ordinary Tor over the extension with the actual completed coefficient H⁰. -/
lemma exists_andre_extension_detects_completedBaseChangeTor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧
      (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (_hC : IsIntegralPerfectoid C p)
        (N : ModuleCat.{u} R) (k : ℕ) (_hN : ∀ x : N, (p : R) ^ k • x = 0)
        (i : ℕ) (s : R),
        let X := (DerivedCompletion.boundedAboveDerivedCompletionFunctor E (p : E)).obj
          ((boundedAboveDerivedBaseChange (algebraMap R E)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))
        let M := (DerivedCategory.homologyFunctor (ModuleCat E) 0).obj X.obj
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
          ∀ x : (((Tor (ModuleCat E) i).obj M).obj
            ((ModuleCat.extendScalars (algebraMap R E)).obj N)), algebraMap R E s • x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, _hdet⟩ :=
    exists_andre_extension_detects_powerTorsion_Tor R p hR
  letI := hEring
  letI := hEalg
  have hφ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R E).toLinearEquiv.symm hflat
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro C _ _ hC N k hN i s
  exact BhattScholze.integralPerfectoid_torCoefficientScalar_eq_zero_iff_completedBaseChangeTor
    p R E C hR hE hC hφ N k hN i s

end SerrePositivity.BhattScholze

end AndreTorDescentPart

section AndrePerfectoidizationTorDescentPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- Choose one extension before the original algebra, its perfectoidization,
the base-changed perfectoidization model, and all power-torsion Tor tests. -/
lemma exists_andre_extension_detects_baseChangedPerfectoidizationTor
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      IsIntegralPerfectoid E p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧
      (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
        (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom)
        (D : Type u) [CommRing D] [Algebra E D] (g : E ⊗[R] A →ₐ[E] D)
        (_hg : IsPerfectoidization p g.toRingHom)
        (N : ModuleCat.{u} R) (k : ℕ) (_hN : ∀ x : N, (p : R) ^ k • x = 0)
        (i : ℕ) (s : R),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 ↔
          ∀ x : (((Tor (ModuleCat E) i).obj (ModuleCat.of E D)).obj
            ((ModuleCat.extendScalars (algebraMap R E)).obj N)), algebraMap R E s • x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, _hdet⟩ :=
    exists_andre_extension_detects_powerTorsion_Tor R p hR
  letI := hEring
  letI := hEalg
  have hφ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R E).toLinearEquiv.symm hflat
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro A C _ _ _ _ f hf D _ _ g hg N k hN i s
  exact BhattScholze.perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    R p E A C hR hE hφ f hf D g hg N k hN i s

end SerrePositivity.BhattScholze

end AndrePerfectoidizationTorDescentPart

section AndrePerfectoidIdealTorDescentPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard

/-- Full ideal Tor annihilation over a specified completely faithfully flat
perfectoid extension descends to the original perfectoidization and ideal. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    (R E A C : Type u) [CommRing R] [CommRing E] [CommRing A] [CommRing C]
    [Algebra R E] [Algebra R A] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hE : IsIntegralPerfectoid E p)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra E D]
    (g : E ⊗[R] A →ₐ[E] D) (hg : IsPerfectoidization p g.toRingHom) (a : R)
    (hTor : ∀ (L : ModuleCat.{u} E) (k : ℕ), (∀ x : L, (p : E) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal E p hE (algebraMap R E a),
        torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  let L := (ModuleCat.extendScalars (algebraMap R E)).obj N
  have hL : ∀ x : L, (p : E) ^ k • x = 0 := by
    simpa only [map_pow, map_natCast] using
      scalarExtension_annihilated (algebraMap R E) ((p : R) ^ k) N hN
  have hsE := _root_.SerrePositivity.BhattScholze.Almost.map_mem_perfectoidIdeal p hR hE (algebraMap R E) a s hs
  have hz := hTor L k hL i hi (algebraMap R E s) hsE
  rw [torCoefficientScalar_algebraMap_eq_smul_id] at hz
  apply (perfectoidization_torCoefficientScalar_eq_zero_iff_baseChangedPerfectoidizationTor
    R p E A C hR hE hflat f hf D g hg N k hN i s).mpr
  intro x
  exact congrArg (fun m => m.hom x) hz

/-- The finite principal cover input on an AIC extension supplies all original
ideal Tor tests. The cover and coefficient models precede the test module. -/
theorem perfectoidIdeal_powerTorsionTorInput_of_baseChanged_aic_principal_cover
    (R E A C : Type u) [CommRing R] [CommRing E] [CommRing A] [CommRing C]
    [Algebra R E] [Algebra R A] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (hE : IsIntegralPerfectoid E p)
    (hAIC : IsAbsolutelyIntegrallyClosed E)
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)))
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (D : Type u) [CommRing D] [Algebra E D]
    (g : E ⊗[R] A →ₐ[E] D) (hg : IsPerfectoidization p g.toRingHom) (a : R)
    (t : Finset (Localization.Away (algebraMap R E a)))
    (ht : Ideal.span (t : Set (Localization.Away (algebraMap R E a))) = ⊤)
    (hlocal : ∀ q : t, ∀ (L : ModuleCat.{u} E) (k : ℕ),
      (∀ x : L, (p : E) ^ k • x = 0) → ∀ i : ℕ, 0 < i →
      ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal E p hE
        (algebraMap R E a * (IsLocalization.Away.sec (algebraMap R E a) q.1).1),
        torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  apply perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    R E A C p hR hE hflat f hf D g hg a
  exact perfectoidIdeal_powerTorsionTorInput_of_aic_principal_cover E p hE hAIC
    (algebraMap R E a) t ht D hlocal

/-- One actual Andre extension suffices for all algebras, generators, specified
perfectoidizations and all original ideal Tor tests; none is chosen per test. -/
theorem exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      ∃ hE : IsIntegralPerfectoid E p,
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) E ∧
      IsAbsolutelyIntegrallyClosed E ∧
      ∃ ρ : E → ℕ → E, (∀ s, ρ s 0 = s) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) ∧
      ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
        (f : A →ₐ[R] C) (_hf : IsPerfectoidization p f.toRingHom)
        (D : Type u) [CommRing D] [Algebra E D] (g : E ⊗[R] A →ₐ[E] D)
        (_hg : IsPerfectoidization p g.toRingHom) (a : R),
        (∀ (L : ModuleCat.{u} E) (k : ℕ), (∀ x : L, (p : E) ^ k • x = 0) →
          ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal E p hE (algebraMap R E a),
            torCoefficientScalarEndomorphism D L i (algebraMap E D s) = 0) →
        ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
          ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
            torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, _hdet⟩ :=
    exists_andre_extension_detects_baseChangedPerfectoidizationTor R p hR
  have hflat' : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (baseChangeScalarModule (algebraMap R E)) :=
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R E).toLinearEquiv.symm hflat
  refine ⟨E, hEring, hEalg, hE, hflat, haic, ρ, hρ0, hρ, ?_⟩
  intro A C _ _ _ _ f hf D _ _ g hg a hTor
  exact perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
    R E A C p hR hE hflat' f hf D g hg a hTor

end SerrePositivity.BhattScholze

end AndrePerfectoidIdealTorDescentPart

section AndreBasePart

namespace SerrePositivity.BhattScholze

/-- 元の R から選ぶ、perfectoid・絶対整閉な André 拡大と実降下用の完全忠実平坦性。
存在を新しい仮定・引用とせず、証明済み BS 著者版 Theorem 7.14 から供給する。 -/
theorem exists_andre_descent_base
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      IsIntegralPerfectoid B p ∧ IsAbsolutelyIntegrallyClosed B ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
        (baseChangeScalarModule (algebraMap R B)) := by
  obtain ⟨B, hB, hRB, hperf, hflat, hAIC⟩ :=
    BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  letI := hB
  letI := hRB
  exact ⟨B, hB, hRB, hperf, hAIC,
    isCompletelyFaithfullyFlat_of_linearEquiv (Ideal.span {(p : R)})
      (algebraSelfRestrictionIso R B).toLinearEquiv.symm hflat⟩

end SerrePositivity.BhattScholze

end AndreBasePart
