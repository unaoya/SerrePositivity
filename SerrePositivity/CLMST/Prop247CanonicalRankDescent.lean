module

public import SerrePositivity.CLMST.Prop247GeneralRank
public import SerrePositivity.CLMST.Prop247RankProductUniversality
public import SerrePositivity.CLMST.Prop247RankData
public import SerrePositivity.CLMST.Prop247CoveredDescent
public import SerrePositivity.CommutativeAlgebra.EtaleAwayTensorBaseChange

/-! # Prop 2.4.7：原典の実一般 rank 四角形からの降下

元の実データと直積単位の普遍性を供給し、残る入力を指定 canonical excision 四角形にする。
原典 E∞ 版 Cor 8.12 自体は宣言・引用せず、その引き戻し性は明示入力のままとする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の全実データと直積普遍単位を供給し、指定 canonical 四角形から元の錐へ降下する。 -/
theorem prop247_exists_canonical_generalRank_descent_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → KLFiniteComparisonExcision B p)
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
          prop247_awayRank B (B ⊗[R] S) (algebraMap R B g) x ∈ t)
        (T : t → CommAlgCat.{u} B)
        (u : ∀ n : t, prop247_rankSourceImage B (B ⊗[R] S)
          (algebraMap R B g) hetaleB n →ₐ[B] T n)
        (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
        (Q : t → CommAlgCat.{u} B)
        (γ : ∀ n : t, T n ⊗[B] (B ⊗[R] S) →ₐ[B] Q n)
        (hγ : ∀ n : t, IsPerfectoidization p (γ n).toRingHom),
        ∃ hProduct : IsPerfectoidization p
          (prop247_rankProductUnit B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ).toRingHom,
          KLCanonicalExcisionSquare hβ hProduct
            (prop247_rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g) →
        ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
          (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
          (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨B, hB, hAIC, hflat, P, β, hβ, t, hcover, T, u, hu, Q, γ, hγ, hassembly⟩ :=
    prop247_exists_generalRank_descent_data R S C p hR hExcision f hf hbounded g hetale
  let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  letI (n : t) : Algebra
      (prop247_rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    (u n).toRingHom.toAlgebra
  letI (n : t) : IsScalarTower B
      (prop247_rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsPerfectoidization p (algebraMap
      (prop247_rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n)) := hu n
  letI (n : t) : Module.Finite B (T n) :=
    (prop247_rankTarget_surjective_finite B (B ⊗[R] S) p hB (algebraMap R B g)
      hetaleB n (T n) (hT n)).2
  have hProduct := prop247_rankProductUnit_isPerfectoidization_of_finite_coefficients
    B (B ⊗[R] S) (fun n => T n) (fun n => Q n) p hB γ hγ
  refine ⟨B, hB, hAIC, hflat, P, β, hβ, t, hcover, T, u, hu, Q, γ, hγ, hProduct, ?_⟩
  intro hPB
  have hk := prop247_rankPerfectoidComparison_ker_of_canonical_excision
    B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ p P β hβ hγ hProduct
    hB (algebraMap R B g) hPB
  apply hassembly
  exact ⟨1, by simpa only [pow_one] using hk⟩

end SerrePositivity.CLMST
