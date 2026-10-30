module

public import SerrePositivity.Asymptotic.SupportedKaroubiTriangulated
public import SerrePositivity.Asymptotic.CompletedHomologyLength
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 商の完備化で支持される全対象への評価

支持部分圏の商との比較を完全三角形と両立させることで、
全対象にホモロジー長・Euler 評価・K₀ 上の準同型を与える。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

instance completedRankHomology_isHomological (q : ℤ) :
    (completedRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  dsimp only [completedRankHomology]
  infer_instance

/-- 計算側の支持部分圏でも、各次数のホモロジーは第零次関手のシフトである。 -/
noncomputable def completedRankHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ completedRankHomology lam hfg z hJ hfin U hU hs 0 ≅
      completedRankHomology lam hfg z hJ hfin U hU hs q := by
  let E := (supportedKaroubiEquivalence (s := s) z).inverse
  let H := completedSupportedHomology lam hfg z hJ hfin U hU hs 0
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (E.commShiftIso q) H ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E
      (completedSupportedHomologyShiftNatIso lam hfg z hJ hfin U hU hs q)

noncomputable instance completedRankHomology_shiftSequence :
    (completedRankHomology lam hfg z hJ hfin U hU hs 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 既存の交代和は共通の Euler 評価に一致する。 -/
lemma completedRankEuler_eq_homologicalEuler
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    completedRankEuler lam hfg z hJ hfin U hU hs X =
      homologicalEuler (lengthQuotientValue lam s U hU hs)
        (completedRankHomology lam hfg z hJ hfin U hU hs 0) X := by
  unfold completedRankEuler completedSupportedEuler homologicalEuler
  congr 1
  funext q
  congr 1
  exact (lengthQuotientValue_iso lam s U hU hs
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)).symm

/-- 共通 Euler 評価に使うシフト列は、完備化後も各対象で有界である。 -/
lemma completedRankHomology_shift_bounded
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((completedRankHomology lam hfg z hJ hfin U hU hs 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := completedRankHomology_bounded lam hfg z hJ hfin U hU hs X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X)⟩

set_option maxHeartbeats 800000 in
-- 二重の商圏と同値の逆関手を含む型の簡約に余裕を与える。
/-- 全支持対象上の Euler 評価は標準的な完全三角形に関して加法的。 -/
lemma completedRankEuler_triangle
    (T : Triangle (supportedCompletedRankQuotient (s := s) z).FullSubcategory)
    (hT : T ∈ distTriang _) :
    completedRankEuler lam hfg z hJ hfin U hU hs T.obj₂ =
      completedRankEuler lam hfg z hJ hfin U hU hs T.obj₁ +
        completedRankEuler lam hfg z hJ hfin U hU hs T.obj₃ := by
  simp only [completedRankEuler_eq_homologicalEuler]
  exact homologicalEuler_triangle (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs) T hT

lemma completedRankEuler_iso
    {X Y : (supportedCompletedRankQuotient (s := s) z).FullSubcategory} (i : X ≅ Y) :
    completedRankEuler lam hfg z hJ hfin U hU hs X =
      completedRankEuler lam hfg z hJ hfin U hU hs Y :=
  completedSupportedEuler_iso lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.mapIso i)

/-- 商の完備化の支持部分圏の K₀ 上に定義される Euler 評価。 -/
noncomputable def completedRankEulerK0 :
    TriangulatedK0 (supportedCompletedRankQuotient (s := s) z).FullSubcategory →+ ℝ :=
  homologicalEulerK0 (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_iso lam s U hU hs) (lengthQuotientValue_add lam s U hU hs)
    (completedRankHomology lam hfg z hJ hfin U hU hs 0)
    (fun X hX ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs X).mpr hX)
    (completedRankHomology_shift_bounded lam hfg z hJ hfin U hU hs)

@[simp] lemma completedRankEulerK0_mk
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    completedRankEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      completedRankEuler lam hfg z hJ hfin U hU hs X := by
  rw [completedRankEulerK0, homologicalEulerK0_mk, completedRankEuler_eq_homologicalEuler]

/-- 商の完備化で支持される対象の第 q 次ホモロジーの非負な実数値。 -/
noncomputable def completedRankBetti
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  lengthQuotientValue lam s U hU hs
    ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj X)

lemma completedRankBetti_nonneg
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ completedRankBetti lam hfg z hJ hfin U hU hs X q := lengthQuotientValue_nonneg ..

lemma completedRankBetti_hasFiniteSupport
    (X : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (completedRankBetti lam hfg z hJ hfin U hU hs X) :=
  completedSupportedBetti_hasFiniteSupport lam hfg z hJ hfin U hU hs _

lemma completedRankBetti_iso
    {X Y : (supportedCompletedRankQuotient (s := s) z).FullSubcategory} (i : X ≅ Y) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs X q =
      completedRankBetti lam hfg z hJ hfin U hU hs Y q :=
  lengthQuotientValue_iso lam s U hU hs
    ((completedRankHomology lam hfg z hJ hfin U hU hs q).mapIso i)

/-- 商で零となった射の錐に対する一段の公式。 -/
lemma completedRankBetti_zero_cone
    (T : Triangle (supportedCompletedRankQuotient (s := s) z).FullSubcategory)
    (hT : T ∈ distTriang _) (hf : T.mor₁ = 0) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs T.obj₃ q =
      completedRankBetti lam hfg z hJ hfin U hU hs T.obj₂ q +
        completedRankBetti lam hfg z hJ hfin U hU hs T.obj₁ (q + 1) := by
  let E := (supportedKaroubiEquivalence (s := s) z).inverse
  exact completedSupportedBetti_zero_cone lam hfg z hJ hfin U hU hs (E.mapTriangle.obj T)
    (E.map_distinguished T hT) (by change E.map T.mor₁ = 0; rw [hf, E.map_zero]) q

/-- 完備化の比較関手の像では、元の支持つき商のホモロジーの長さに一致する。 -/
lemma completedRankBetti_obj
    (X : SupportedSequenceRankQuotient (s := s) z) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      ((supportedKaroubiFunctor z).obj ((toKaroubi _).obj X)) q =
      lengthQuotientValue lam s U hU hs
        ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj X) := by
  let E := supportedKaroubiEquivalence (s := s) z
  exact lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).mapIso
      (E.unitIso.symm.app ((toKaroubi _).obj X)) ≪≫
        (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app X)

end SerrePositivity.Asymptotic
