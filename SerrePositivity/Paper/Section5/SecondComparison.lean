module

public import SerrePositivity.Paper.Section4.SymmetricComparison
public import SerrePositivity.Asymptotic.OrdinaryTwistEvaluation

/-! # 共通の対称比較から第二比較へ

論文の支持圏の実際の群作用を使う。通常評価の群不変性により、
共通の共役和比較の一方が群の位数倍になる。
有限近似側と正則基底側の支持は異なってよく、同じ複体列の評価を移して接続する。
Koszul Euler 数の一致と不変類の降下は、個別の入力として明示する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing T] [Nontrivial T] [Algebra A T] [CommRing C] [Nontrivial C]
  {G : Type u} [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (ψ : T →+* C) {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (a : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (ψ ∘ algebraMap A T ∘ a))
  (hord : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap A T ∘ a))
  (ha : Ideal.span (Set.range a) = maximalIdeal A) (hKos : IsKoszulResolution a)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ a) =
    LengthAlgebra.koszulEuler lam (ψ ∘ algebraMap A T ∘ a))
  (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
    (∀ g : G, g • y = y) → ∃ (n : ℕ)
      (x : TriangulatedK0 (paperSupportedRank (s := s) a).FullSubcategory),
      0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) a) x)

set_option maxHeartbeats 800000 in
-- 三つの係数環の支持圏と、実際の群作用をもつ K₀ の比較に必要。
include ha hKos hc hdesc in
/-- 第二比較の共通部分。通常 Euler 数の群の位数倍が、正規化評価の共役和に等しい。 -/
theorem secondComparison_of_complex
    (K : CochainComplex (FreeSequence T s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (algebraMap A T ∘ a)
      ((paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK))) :
    (Fintype.card G : ℝ) * paperRankEulerK0 (NormalizedLength.ordinary T) Submodule.fg_bot
      (algebraMap A T ∘ a) bot_le hord U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
      (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩) := by
  have he := Section4.symmetricPaperEuler_conjSum_eq (algebraMap A T) (RingHom.id T) ψ
    (NormalizedLength.ordinary T) lam Submodule.fg_bot hfg a bot_le hJ hord hfin
    ha hKos U hU hs hc hdesc
    (TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩)
  rw [paperBaseChangeEulerK0_id] at he
  have hconst (g : G) := paperOrdinaryEulerK0_smul U hU hs K hK a hord h g
  simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he

variable {B : Type u} [CommRing B] [Nontrivial B] (φ : B →+* T)
  {f : ℕ} (z : Fin f → B)
  (hordB : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (φ ∘ z))

set_option maxHeartbeats 800000 in
-- 近似側と正則基底側の支持部分圏をまたぐ評価の比較に必要。
include hord ha hKos hc hdesc in
/-- 有限近似側のパラメータで計算した通常評価を、第二比較の支持圏へ移す。 -/
theorem secondComparison_of_baseChangedComplex
    (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hB : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
    (hT : paperSupportedRank (algebraMap A T ∘ a) ((paperSequenceFunctor T s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    (Fintype.card G : ℝ) * paperBaseChangeEulerK0 φ z (NormalizedLength.ordinary T)
      Submodule.fg_bot bot_le hordB U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), hB⟩) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
      (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj
        (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
          (changeRing_strictlyBounded φ K hK)), hT⟩) := by
  rw [paperBaseChangeEulerK0_complex_support_change φ z (NormalizedLength.ordinary T)
    Submodule.fg_bot bot_le hordB U hU hs (algebraMap A T ∘ a) bot_le hord K hK hB hT]
  exact secondComparison_of_complex ψ lam hfg a hJ hfin hord ha hKos U hU hs hc hdesc _ _ hT

end SerrePositivity.Section5
