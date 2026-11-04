module

public import SerrePositivity.BhattScholze.Andre.TorDescent
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.ComponentExcision
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Descent.Uniform
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.TargetComparison

/-! # 一般の階数からの降下

## 概要

André 拡大・通常のテンソルの perfectoid 化・原典の有限な階数の分解と各普遍単位を選び、終域の比較の核の冪零化を明示した降下のデータを作る（`exists_generalRank_descent_data`）。直積の単位の普遍性を供給して、残る入力を標準 excision の四角にする（`exists_canonical_generalRank_descent_data`）。

## 方針

全剰余段の共通指数と元の錐への降下は `Descent/Uniform` に接続する。

## 規約

CLMST Prop 2.4.7。原典の E∞ 版の Cor 8.12 は宣言も引用もせず、引き戻し性は明示的な入力。旧 `CLMST/Prop247GeneralRank`・`Prop247CanonicalRankDescent`。

## 使われ方

`Proof`。
-/

@[expose] public noncomputable section

universe u

section Prop247GeneralRankPart

namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の一般 rank の実対象を全て選び、残る終域比較から元の実錐へ降下する。
André 拡大・rank 対象・各 perfectoid 化の存在は追加仮定にしない。 -/
theorem exists_generalRank_descent_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → BhattScholze.KLFiniteComparisonExcision B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) :
    ∃ (B : CommAlgCat.{u} R),
      let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
      ∃ (_ : IsIntegralPerfectoid B p) (_ : IsAbsolutelyIntegrallyClosed B)
        (_ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
          (baseChangeScalarModule (algebraMap R B)))
        (P : CommAlgCat.{u} B) (β : B ⊗[R] S →ₐ[B] P)
        (hβ : IsPerfectoidization p β.toRingHom)
        (t : Finset ℕ)
        (_ : ∀ x : PrimeSpectrum.basicOpen (algebraMap R B g),
          awayRank B (B ⊗[R] S) (algebraMap R B g) x ∈ t)
        (T : t → CommAlgCat.{u} B)
        (u : ∀ n : t, rankSourceImage B (B ⊗[R] S)
          (algebraMap R B g) hetaleB n →ₐ[B] T n)
        (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
        (Q : t → CommAlgCat.{u} B)
        (γ : ∀ n : t, T n ⊗[B] (B ⊗[R] S) →ₐ[B] Q n)
        (hγ : ∀ n : t, IsPerfectoidization p (γ n).toRingHom),
        (∃ b : ℕ, ∀ x : (rankPerfectoidComparison B (B ⊗[R] S)
          (fun n => T n) p P β hβ (fun n => Q n) γ hγ).toLinearMap.ker,
          (algebraMap R B g) ^ b • x = 0) →
        ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
          (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
          (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨B, hB, hRB, hperf, hAIC, hflat⟩ := BhattScholze.exists_andre_descent_base R p hR
  letI := hB
  letI := hRB
  let A := B ⊗[R] S
  obtain ⟨P, hP, β₀, hβ₀⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral B A p hperf
  letI := hP
  letI : Algebra B P := (β₀.comp (algebraMap B A)).toAlgebra
  let β : A →ₐ[B] P := { β₀ with commutes' := fun _ => rfl }
  have hβ : IsPerfectoidization p β.toRingHom := hβ₀
  have hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  obtain ⟨t, hcover, T, u, hu, Q, γ, hγ, hassembly⟩ :=
    aic_exists_rank_comparison_data B A P p hperf hAIC hExcision
      (algebraMap R B g) hetaleB β hβ
  refine ⟨CommAlgCat.of R B, hperf, hAIC, hflat, CommAlgCat.of B P,
    β, hβ, t, hcover, T, u, hu, Q, γ, hγ, ?_⟩
  intro htk
  obtain ⟨q, hq, _hk, _hc⟩ := hassembly htk
  have hU := uniform_of_standard_fixed_cone R S B C P p hR hperf f hf hbounded
    g β hβ hflat.1 ⟨q, hq⟩
  exact moduleMapConeIsogeny_descent (algebraMap R B) (p : R) hflat f.toLinearMap
    (cone_isComplete_of_integralPerfectoid_target R S p hR C hf.1 f.toLinearMap) g hU

end SerrePositivity.CLMST

end Prop247GeneralRankPart

section Prop247CanonicalRankDescentPart

namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の全実データと直積普遍単位を供給し、指定 canonical 四角形から元の錐へ降下する。 -/
theorem exists_canonical_generalRank_descent_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → BhattScholze.KLFiniteComparisonExcision B p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) :
    ∃ (B : CommAlgCat.{u} R),
      let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
      ∃ (_ : IsIntegralPerfectoid B p) (_ : IsAbsolutelyIntegrallyClosed B)
        (_ : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
          (baseChangeScalarModule (algebraMap R B)))
        (P : CommAlgCat.{u} B) (β : B ⊗[R] S →ₐ[B] P)
        (hβ : IsPerfectoidization p β.toRingHom)
        (t : Finset ℕ)
        (_ : ∀ x : PrimeSpectrum.basicOpen (algebraMap R B g),
          awayRank B (B ⊗[R] S) (algebraMap R B g) x ∈ t)
        (T : t → CommAlgCat.{u} B)
        (u : ∀ n : t, rankSourceImage B (B ⊗[R] S)
          (algebraMap R B g) hetaleB n →ₐ[B] T n)
        (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
        (Q : t → CommAlgCat.{u} B)
        (γ : ∀ n : t, T n ⊗[B] (B ⊗[R] S) →ₐ[B] Q n)
        (hγ : ∀ n : t, IsPerfectoidization p (γ n).toRingHom),
        ∃ hProduct : IsPerfectoidization p
          (rankProductUnit B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ).toRingHom,
          BhattScholze.KLCanonicalExcisionSquare hβ hProduct
            (rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g) →
        ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
          (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
          (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨B, hB, hAIC, hflat, P, β, hβ, t, hcover, T, u, hu, Q, γ, hγ, hassembly⟩ :=
    exists_generalRank_descent_data R S C p hR hExcision f hf hbounded g hetale
  let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  letI (n : t) : Algebra
      (rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    (u n).toRingHom.toAlgebra
  letI (n : t) : IsScalarTower B
      (rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsPerfectoidization p (algebraMap
      (rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n)) := hu n
  letI (n : t) : Module.Finite B (T n) :=
    (rankTarget_surjective_finite B (B ⊗[R] S) p hB (algebraMap R B g)
      hetaleB n (T n) (hT n)).2
  have hProduct := rankProductUnit_isPerfectoidization_of_finite_coefficients
    B (B ⊗[R] S) (fun n => T n) (fun n => Q n) p hB γ hγ
  refine ⟨B, hB, hAIC, hflat, P, β, hβ, t, hcover, T, u, hu, Q, γ, hγ, hProduct, ?_⟩
  intro hPB
  have hk := rankPerfectoidComparison_ker_of_canonical_excision
    B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ p P β hβ hγ hProduct
    hB (algebraMap R B g) hPB
  apply hassembly
  exact ⟨1, by simpa only [pow_one] using hk⟩

end SerrePositivity.CLMST

end Prop247CanonicalRankDescentPart
