module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Cover
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient

/-! # perfectoid イデアルの Tor の入力の判定法

## 概要

perfectoid イデアルの冪ねじれ Tor の入力（正の次数の Tor の係数作用の零化）について、互換根による同値（`perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots`）、有限自由な almost 比較からの導出、環の引き戻しの四角（excision）に沿った移送（`perfectoidIdeal_TorInput_iff_of_isPullback`）を与える。
BS 著者版 §10.1 の perfectoid 核による零化を、CLMST の Tor の入力に移す判定法を与える。

## 方針

検査加群と元の係数の自己準同型を保ったまま、互換根の完備化と almost 比較の向きによらない移送（`PerfectoidIdeal/CompletedQuotient`）を使う。

## 規約

検査加群に有限生成性・完備性・平坦性・正則性は仮定しない。残る数学的な入力は指定した圏論的な環の引き戻しだけ。旧 `CLMST/PerfectoidIdealTorRoots`・`PerfectoidIdealTorComparison`・`PerfectoidIdealExcisionTor`（CLMST の主経路からは使われないが、一般論として残した。2026-11-02 決定）。

## 使われ方

いまは利用者がない（Prop 2.4.9(a) の別の経路）。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIdealTorRootsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C]
include hρ

/-- Original coefficient zero actions on Tor are detected by the given compatible roots. -/
theorem perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
      ∀ n, torCoefficientScalarEndomorphism C N i (algebraMap R C (ρ n)) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C)
  have hp : (p : R) ^ k ∈ J :=
    torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i ((p : R) ^ k) hN
  change (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0) ≤ J) ↔ ∀ n, ρ n ∈ J
  exact _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_le_iff_compatible_roots R p hR ρ hρ J k hp

/-- The full power-torsion Tor input is equivalent to tests on every compatible root. -/
theorem perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots :
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR (ρ 0),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ n,
        torCoefficientScalarEndomorphism C N i (algebraMap R C (ρ n)) = 0) := by
  constructor
  · intro h N k hN i hi
    exact (perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
      R p hR ρ hρ C N k hN i).mp (h N k hN i hi)
  · intro h N k hN i hi
    exact (perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
      R p hR ρ hρ C N k hN i).mpr (h N k hN i hi)

end SerrePositivity.BhattScholze

end PerfectoidIdealTorRootsPart

section PerfectoidIdealTorComparisonPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- A finite free comparison almost isomorphism supplies all original power-torsion Tor tests.
The comparison is explicit; its existence and descent from an extension are separate inputs. -/
lemma perfectoidIdeal_powerTorsionTorInput_of_finiteFree_comparison
    (C : Type u) [CommRing C] [Algebra R C]
    (r : ℕ) (f : C →ₗ[R] (Fin r → R))
    (hc : ∀ a ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g, ∀ x : f.ker, b • x = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  intro N k hN i hi s hs
  exact torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison r f
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hc hk N ((p : R) ^ k) hN
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g k) i hi s hs

end SerrePositivity.BhattScholze

end PerfectoidIdealTorComparisonPart

section PerfectoidIdealExcisionTorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Actual excision transports original ideal Tor tests in every degree, for
arbitrary p-power-torsion test modules. -/
theorem perfectoidIdeal_TorInput_iff_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
      torCoefficientScalarEndomorphism A N i (algebraMap R A s) = 0) ↔
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g,
      torCoefficientScalarEndomorphism B N i (algebraMap R B s) = 0) := by
  obtain ⟨hk, hc⟩ := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_ker_coker_annihilated_of_isPullback
    hR f l r b hPB hC g hg
  exact torCoefficientIdeal_eq_zero_iff_of_almost_comparison f.toLinearMap
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hk hc N ((p : R) ^ k) hN
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g k) i

end SerrePositivity.BhattScholze

end PerfectoidIdealExcisionTorPart
