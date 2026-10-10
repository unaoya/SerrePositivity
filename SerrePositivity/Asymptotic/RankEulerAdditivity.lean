module

public import SerrePositivity.Asymptotic.RankEuler
public import SerrePositivity.Asymptotic.RankHomologyShift
public import SerrePositivity.CategoryTheory.HomologicalEuler

/-!
# 支持つきランク商の Euler 評価の三角加法性

次数別のホモロジー評価を第零ホモロジーのシフト列と比較し、
有界ホモロジー関手の Euler 評価の一般定理を適用する。
これにより冪等完備化前の支持つきランク商の `K₀` 上に準同型を得る。
Karoubi 包絡の三角構造と、その `K₀` への延長は別途必要である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

noncomputable instance supportedRankHomology_shiftSequence :
    (supportedRankHomology lam hfg z hJ hfin U hU hs 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- ランク商の交代和は、共通のホモロジー的 Euler 評価である。 -/
lemma supportedRankEuler_eq_homologicalEuler
    (X : SupportedSequenceRankQuotient (s := s) z) :
    supportedRankEuler lam hfg z hJ hfin U hU hs X =
      homologicalEuler (lengthQuotientValue lam s U hU hs)
        (supportedRankHomology lam hfg z hJ hfin U hU hs 0) X := by
  unfold supportedRankEuler homologicalEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    (supportedRankHomologyShiftIso lam hfg z hJ hfin U hU hs X q).symm

/-- 第零次関手のシフト列は各対象で有界である。 -/
lemma supportedRankHomology_shift_bounded
    (X : SupportedSequenceRankQuotient (s := s) z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((supportedRankHomology lam hfg z hJ hfin U hU hs 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := supportedRankHomology_bounded lam hfg z hJ hfin U hU hs X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    (supportedRankHomologyShiftIso lam hfg z hJ hfin U hU hs X q)⟩

set_option synthInstance.maxSize 512 in
/-- 支持つき Verdier 商の Euler 評価は完全三角形に対して加法的である。 -/
lemma supportedRankEuler_triangle (T : Triangle (SupportedSequenceRankQuotient (s := s) z))
    (hT : T ∈ distTriang _) :
    supportedRankEuler lam hfg z hJ hfin U hU hs T.obj₂ =
      supportedRankEuler lam hfg z hJ hfin U hU hs T.obj₁ +
        supportedRankEuler lam hfg z hJ hfin U hU hs T.obj₃ := by
  simp only [supportedRankEuler_eq_homologicalEuler]
  exact homologicalEuler_triangle (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (supportedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (supportedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs) T hT

/-- 支持つきランク商の Grothendieck 群上に降下した Euler 評価。 -/
noncomputable def supportedRankEulerK0 :
    TriangulatedK0 (SupportedSequenceRankQuotient (s := s) z) →+ ℝ :=
  homologicalEulerK0 (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (supportedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (supportedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs)

/-- Grothendieck 類への評価は、対象上で構成した Euler 評価と一致する。 -/
@[simp] lemma supportedRankEulerK0_mk (X : SupportedSequenceRankQuotient (s := s) z) :
    supportedRankEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      supportedRankEuler lam hfg z hJ hfin U hU hs X := by
  rw [supportedRankEulerK0, homologicalEulerK0_mk, supportedRankEuler_eq_homologicalEuler]

end SerrePositivity.Asymptotic
