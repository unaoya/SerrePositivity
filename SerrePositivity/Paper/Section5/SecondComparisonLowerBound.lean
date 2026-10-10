module

public import SerrePositivity.Paper.Section5.SecondComparison
public import SerrePositivity.Asymptotic.PaperTwistLowerBound

/-! # 第二比較と共通の Euler 下界

極小性から得た同じ下界を、各共役の正規化評価と、比較元の通常評価の両方へ渡す。
通常評価の下界は、共通の比較定理と有限和の単調性から導く。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory CategoryTheory.Limits Filter IsLocalRing Asymptotic

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing T] [Nontrivial T] [Algebra A T] [CommRing C] [Nontrivial C]
  {G : Type u} [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
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
-- 共役和の評価と各共役の下界を、同じ支持つき K₀ の元について比較する。
include ha hKos hc hdesc in
/-- 各共役の下界は、第二比較により通常 Euler 数にも成り立つ。 -/
theorem secondComparison_minimal_lower_bound
    (K : CochainComplex (FreeSequence T s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (algebraMap A T ∘ a)
      ((paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, algebraMap A T (a j) ^ v •
      𝟙 ((paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ ψ (algebraMap A T (a j)) ^ v) i) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal T) (Q : Ideal C) (hIQ : ∀ (g : G) r, r ∈ I → ψ (g • r) ∈ Q)
    (hQ : IsPowTorsion J (C ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → T) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, algebraMap A T (a j) ^ v ∈ I) :
    (∀ g : G, (lam.len (C ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
        (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩)) ∧
    (lam.len (C ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperRankEulerK0 (NormalizedLength.ordinary T) Submodule.fg_bot (algebraMap A T ∘ a)
        bot_le hord U hU hs
        (TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩) := by
  let := Fintype.ofFinite G
  have hlower (g : G) := paperBaseChangeEuler_smul_minimal_lower_bound ψ a lam hfg hJ hfin
    U hU hs K hK h v hv hx hzero hbound I Q g (hIQ g) hQ hmin hzI
  refine ⟨hlower, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun g _ ↦ hlower g)
  have he := secondComparison_of_complex ψ lam hfg a hJ hfin hord ha hKos U hU hs hc hdesc K hK h
  rw [← he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  nlinarith

end SerrePositivity.Section5
