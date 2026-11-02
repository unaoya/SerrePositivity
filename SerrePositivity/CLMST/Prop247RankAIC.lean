module

public import SerrePositivity.CLMST.Prop247RankTargets
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic

/-! # Prop 2.4.7：André 拡大の絶対整閉性を実 rank 対象へ渡す

各 Ri の指定 perfectoid 化 Ti は元の基底の全射像である。
既存の全射像の一般論を適用し、定 rank の局所分裂で使う絶対整閉性を供給する。
Cor 8.12 や perfectoid 化後の almost 比較は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST

/-- André 基底の各実 rank 対象は絶対整閉である。Ri の有限表示性は不要。 -/
theorem prop247_rankTarget_isAbsolutelyIntegrallyClosed
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (hf : IsPerfectoidization p
      (algebraMap (openSectionImage R (rankOpen R S g hetale n)) T)) :
    IsAbsolutelyIntegrallyClosed T :=
  hAIC.of_surjective (algebraMap R T)
    (prop247_rankTarget_surjective_finite R S p hR g hetale n T hf).1

open scoped TensorProduct

/-- 元の rank 像の perfectoid 化を絶対整閉性と実底変換の定 rank とともに供給する。
原典の rank 0・空の rank 部分も含み、新しい存在引用を使わない。 -/
theorem prop247_rankImage_exists_aic_perfectoid_target
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    let I := openSectionImage R (rankOpen R S g hetale n)
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra I T),
      IsScalarTower R I T ∧ IsPerfectoidization p (algebraMap I T) ∧
      IsAbsolutelyIntegrallyClosed T ∧
      Function.Surjective (algebraMap R T) ∧ Module.Finite R T ∧
      ∀ x : PrimeSpectrum.basicOpen (algebraMap R T g),
        awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  obtain ⟨T, hT, hRT, hIT, htower, hf, hs, hfinite, hrank⟩ :=
    prop247_rankImage_exists_perfectoid_target R S p hR g hetale n
  letI := hT
  letI := hRT
  letI := hIT
  letI := htower
  exact ⟨T, hT, hRT, hIT, htower, hf,
    prop247_rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n T hf,
    hs, hfinite, hrank⟩

end SerrePositivity.CLMST
