module

public import SerrePositivity.CLMST.Prop247ConstantRankExcision
public import SerrePositivity.CLMST.Prop247RankAIC
public import SerrePositivity.CLMST.Prop247AicRankAssembly
public import SerrePositivity.CommutativeAlgebra.EtaleAwayTensorBaseChange

/-! # Prop 2.4.7：原典の各実 rank 成分への定 rank 証明の適用

各 Si=Ti⊗R S の元の有限性・有限表示性・定 rank と Ti の絶対整閉性を供給する。
指定した βi と元の R 作用の核・余核へ結論を戻す。
未供給の excision は明示入力であり、選択は既存 B-I のみを使用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の各実 rank 成分の指定単位について、KL excision から元の R 作用の冪零化を得る。
Si の bounded torsion は不要である。 -/
theorem prop247_aic_rankComponent_annihilators_of_excision
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (n : ℕ) (T P : Type u) [CommRing T] [CommRing P] [Algebra R T] [Algebra R P]
    [Algebra (prop247_rankSourceImage R S g hetale n) T]
    [IsScalarTower R (prop247_rankSourceImage R S g hetale n) T]
    (hT : IsPerfectoidization p (algebraMap (prop247_rankSourceImage R S g hetale n) T))
    (hExcision : KLFiniteComparisonExcision T p)
    (β : T ⊗[R] S →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom) :
    ∃ q : ℕ, (∀ x : β.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : P ⧸ β.toLinearMap.range, g ^ q • y = 0) := by
  letI := hR.isReduced R p
  letI : Algebra T P := (β.toRingHom.comp (algebraMap T (T ⊗[R] S))).toAlgebra
  letI : IsScalarTower R T P := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R P r = β (algebraMap T (T ⊗[R] S) (algebraMap R T r))
    rw [← IsScalarTower.algebraMap_apply R T (T ⊗[R] S), β.commutes]
  let βT : T ⊗[R] S →ₐ[T] P := { β.toRingHom with commutes' := fun _ => rfl }
  have hβT : IsPerfectoidization p βT.toRingHom := hβ
  have hAIC_T := prop247_rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n T hT
  have hRank := prop247_awayRank_baseChange_over_rankImage R S g hetale n T
  have hEtale := etaleAway_tensor_baseChange (R := R) (A := S) (B := T) g hetale
  obtain ⟨q, hq⟩ := prop247_aic_constantRank_isogeny_of_finiteComparison_excision p hT.1
    hAIC_T hExcision (algebraMap R T g) βT hβT hEtale n hRank
  obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates T βT.toLinearMap
    (algebraMap R T g) q hq
  refine ⟨q, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change g ^ q • (x : T ⊗[R] S) = 0
    have h := congrArg Subtype.val (hk ⟨(x : T ⊗[R] S), x.property⟩)
    change (algebraMap R T g) ^ q • (x : T ⊗[R] S) = 0 at h
    simpa only [← map_pow, algebraMap_smul] using h
  · intro y
    obtain ⟨y, rfl⟩ := β.toLinearMap.range.mkQ_surjective y
    have hy : (algebraMap R T g) ^ q • y ∈ βT.toLinearMap.range := by
      apply (Submodule.Quotient.mk_eq_zero βT.toLinearMap.range).mp
      exact (βT.toLinearMap.range.mkQ.map_smul ((algebraMap R T g) ^ q) y).trans (hc _)
    obtain ⟨x, hx⟩ := hy
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero β.toLinearMap.range).mpr
    refine ⟨x, ?_⟩
    change β x = g ^ q • y
    change β x = (algebraMap R T g) ^ q • y at hx
    simpa only [← map_pow, algebraMap_smul] using hx

/-- 元の実 rank 分解に各定 rank 証明を適用する。
成分 isogeny と係数零化を構成し、残る入力は元の終域比較の核の冪零化だけである。 -/
theorem prop247_aic_isogeny_of_rank_component_excision
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]
    (hT : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)))
    (hExcision : ∀ n : t, KLFiniteComparisonExcision (T n) p)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : t → Type u) [∀ n : t, CommRing (P n)] [∀ n : t, Algebra R (P n)]
    (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
    (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom)
    (htk : ∃ b : ℕ, ∀ x :
      (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  apply prop247_aic_isogeny_of_rank_comparisons R S p hR hAIC g hetale t ht T hT
    C f hf P β hβ htk
  intro n
  exact prop247_aic_rankComponent_annihilators_of_excision R S p hR hAIC g hetale n
    (T n) (P n) (hT n) (hExcision n) (β n) (hβ n)

end SerrePositivity.CLMST
