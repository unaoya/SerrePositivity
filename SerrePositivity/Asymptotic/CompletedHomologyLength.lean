module
public import SerrePositivity.CategoryTheory.AlternatingSum

public import SerrePositivity.Asymptotic.CompletedEulerAdditivity
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 完備化後の非負ホモロジー長と零写像の錐 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 512

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 完備化した支持つきランク商の cochain 第 q 次ホモロジーの長さ。 -/
noncomputable def completedSupportedBetti
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) (q : ℤ) : ℝ :=
  lengthQuotientValue lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj X)

lemma completedSupportedBetti_nonneg
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) (q : ℤ) :
    0 ≤ completedSupportedBetti lam hfg z hJ hfin U hU hs X q :=
  lengthQuotientValue_nonneg ..

lemma completedSupportedBetti_iso
    {X Y : Karoubi (SupportedSequenceRankQuotient (s := s) z)} (i : X ≅ Y) (q : ℤ) :
    completedSupportedBetti lam hfg z hJ hfin U hU hs X q =
      completedSupportedBetti lam hfg z hJ hfin U hU hs Y q :=
  lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).mapIso i)

lemma completedSupportedBetti_bounded
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) →
      completedSupportedBetti lam hfg z hJ hfin U hU hs X q = 0 := by
  obtain ⟨a, b, hab⟩ := completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs X
  exact ⟨a, b, fun q hq ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mpr (hab q hq)⟩

lemma completedSupportedBetti_hasFiniteSupport
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    Function.HasFiniteSupport (completedSupportedBetti lam hfg z hJ hfin U hU hs X) := by
  obtain ⟨a, b, hab⟩ := completedSupportedBetti_bounded lam hfg z hJ hfin U hU hs X
  exact finiteSupport_of_bounded_zero _ a b hab

/-- 商で第一射が零になれば、完備化後の非負評価にも錐の漸化式が成り立つ。 -/
lemma completedSupportedBetti_zero_cone
    (T : Triangle (Karoubi (SupportedSequenceRankQuotient (s := s) z)))
    (hT : T ∈ distTriang _) (hf : T.mor₁ = 0) (q : ℤ) :
    completedSupportedBetti lam hfg z hJ hfin U hU hs T.obj₃ q =
      completedSupportedBetti lam hfg z hJ hfin U hU hs T.obj₂ q +
        completedSupportedBetti lam hfg z hJ hfin U hU hs T.obj₁ (q + 1) := by
  let F := completedSupportedHomology lam hfg z hJ hfin U hU hs 0
  let := Functor.ShiftSequence.tautological F ℤ
  have he (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) (q : ℤ) :
      lengthQuotientValue lam s U hU hs ((F.shift q).obj X) =
        completedSupportedBetti lam hfg z hJ hfin U hU hs X q :=
    lengthQuotientValue_iso lam s U hU hs
      ((completedSupportedHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)
  simpa only [he] using homologyLength_zero_cone F (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_add lam s U hU hs) T hT hf q

end SerrePositivity.Asymptotic
