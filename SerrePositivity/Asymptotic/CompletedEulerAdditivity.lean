module

public import SerrePositivity.Asymptotic.RankEulerAdditivity
public import SerrePositivity.Asymptotic.RankHomologyShiftNatural

/-! # 冪等完備化後の Euler 評価と Grothendieck 群

完備化後に現れる直和因子も含めて、標準的な完全三角形に関する
Euler 評価の加法性を証明する。
-/

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

noncomputable instance completedSupportedHomology_shiftSequence :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- Karoubi 包絡上の交代和も共通 Euler 評価に一致する。 -/
lemma completedSupportedEuler_eq_homologicalEuler
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs X =
      homologicalEuler (lengthQuotientValue lam s U hU hs)
        (completedSupportedHomology lam hfg z hJ hfin U hU hs 0) X := by
  unfold completedSupportedEuler homologicalEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X).symm

/-- Karoubi 包絡でも、共通 Euler 構成に使うシフト列は対象ごとに有界である。 -/
lemma completedSupportedHomology_shift_bounded
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((completedSupportedHomology lam hfg z hJ hfin U hU hs 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    ((completedSupportedHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)⟩

/-- Karoubi 包絡上の Euler 評価は完全三角形に対して加法的。 -/
lemma completedSupportedEuler_triangle
    (T : Triangle (Karoubi (SupportedSequenceRankQuotient (s := s) z)))
    (hT : T ∈ distTriang _) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs T.obj₂ =
      completedSupportedEuler lam hfg z hJ hfin U hU hs T.obj₁ +
        completedSupportedEuler lam hfg z hJ hfin U hU hs T.obj₃ := by
  simp only [completedSupportedEuler_eq_homologicalEuler]
  exact homologicalEuler_triangle (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedSupportedHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedSupportedHomology_shift_bounded lam hfg z hJ hfin U hU hs) T hT

/-- 完備化した支持つきランク商の Grothendieck 群上の Euler 評価。 -/
noncomputable def completedSupportedEulerK0 :
    TriangulatedK0 (Karoubi (SupportedSequenceRankQuotient (s := s) z)) →+ ℝ :=
  homologicalEulerK0 (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedSupportedHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedSupportedHomology_shift_bounded lam hfg z hJ hfin U hU hs)

@[simp] lemma completedSupportedEulerK0_mk
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      completedSupportedEuler lam hfg z hJ hfin U hU hs X := by
  rw [completedSupportedEulerK0, homologicalEulerK0_mk,
    completedSupportedEuler_eq_homologicalEuler]

/-- 標準包含の誘導する K₀ 写像に沿った制限は元の Euler 評価。 -/
lemma completedSupportedEulerK0_toKaroubi :
    (completedSupportedEulerK0 lam hfg z hJ hfin U hU hs).comp
      (TriangulatedK0.map (toKaroubi _)) =
        supportedRankEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedSupportedEulerK0_mk, supportedRankEulerK0_mk, completedSupportedEuler_obj]

end SerrePositivity.Asymptotic
