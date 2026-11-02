module

public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.CategoryTheory.Euler
public import SerrePositivity.Asymptotic.RankBaseChange
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # ランク商の Euler 評価

## 概要

長さの Serre 商に値を持つホモロジー関手の有限な交代和として、台を持つランク商の対象の Euler 評価を定め、実際の自由複体の列の像では各段の Euler 評価の正規化超極限に一致することを示す。三角加法性から K₀ 上の準同型を作り、代表複体の Euler 比較をランク商へ移し、冪等完備化の後の加法性・比較・非負のホモロジー長・K₀ の階数倍の公式を与える。

## 方針

次数別のホモロジーを第零ホモロジーのシフト列と比べ、CategoryTheory/Euler の一般定理を当てる。

## 規約

対象上の評価と K₀ 上の準同型を区別する。

## 使われ方

`Completed`・`Minimal`、Paper/Section4。
-/

@[expose] public noncomputable section

universe u

section RankEulerPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter
open scoped BigOperators

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 支持つきランク商の対象上の Euler 評価。 -/
noncomputable def supportedRankEuler (P : SupportedSequenceRankQuotient (s := s) z) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P)

/-- 冪等完備化した支持つきランク商の対象上の Euler 評価。 -/
noncomputable def completedSupportedEuler
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P)

/-- 商の冪等完備化で初めて台をもつ対象も含めた Euler 評価。 -/
noncomputable def completedRankEuler
    (P : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) : ℝ :=
  completedSupportedEuler lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.obj P)

/-- 完備化した評価の交代和は実際に有限支持である。 -/
lemma completedSupportedEuler_hasFiniteSupport
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    Function.HasFiniteSupport (fun q : ℤ ↦ ((q.negOnePow : ℤ) : ℝ) *
      lengthQuotientValue lam s U hU hs
        ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P)) := by
  obtain ⟨a, b, hab⟩ := completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs P
  apply finiteSupport_of_bounded_zero _ a b
  intro q hq
  have hz := (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mpr (hab q hq)
  simp only [hz, mul_zero]

/-- 冪等完備化前の対象では元の Euler 評価と一致する。 -/
lemma completedSupportedEuler_obj (P : SupportedSequenceRankQuotient (s := s) z) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs ((toKaroubi _).obj P) =
      supportedRankEuler lam hfg z hJ hfin U hU hs P := by
  unfold completedSupportedEuler supportedRankEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app P)

/-- 商上の Euler 評価は同型で不変である。 -/
lemma supportedRankEuler_iso {P Q : SupportedSequenceRankQuotient (s := s) z} (i : P ≅ Q) :
    supportedRankEuler lam hfg z hJ hfin U hU hs P =
      supportedRankEuler lam hfg z hJ hfin U hU hs Q := by
  unfold supportedRankEuler
  congr 1
  funext q
  rw [lengthQuotientValue_iso lam s U hU hs
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).mapIso i)]

/-- 冪等完備化後の Euler 評価も同型で不変である。 -/
lemma completedSupportedEuler_iso
    {P Q : Karoubi (SupportedSequenceRankQuotient (s := s) z)} (i : P ≅ Q) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs P =
      completedSupportedEuler lam hfg z hJ hfin U hU hs Q := by
  unfold completedSupportedEuler
  congr 1
  funext q
  rw [lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).mapIso i)]

/-- 形式的直和因子の Euler 評価は、射影の誘導するホモロジーの像の長さの交代和である。 -/
lemma completedSupportedEuler_image
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs P =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
        (Abelian.image ((supportedRankHomology lam hfg z hJ hfin U hU hs q).map P.p)) := by
  unfold completedSupportedEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    (completedSupportedHomologyImageIso lam hfg z hJ hfin U hU hs P q)

/-- 実際の支持つき複体列のホモロジーの評価は、各段の長さの超極限である。 -/
lemma supportedRankHomology_length_complex
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) (q : ℤ) :
    lengthQuotientValue lam s U hU hs
      ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
          ⟨sequenceHomotopyObj K hK, hzK⟩)) =
      normalizedLimit U s (fun n ↦ (lam.len (((evaluateComplex n).obj K).homology q)).toReal) := by
  refine (lengthQuotientValue_iso lam s U hU hs
    ((supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app
      ⟨sequenceHomotopyObj K hK, hzK⟩)).trans ?_
  change sequenceLength lam s U _ = _
  unfold sequenceLength
  congr 1
  funext n
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    (((moduleSequenceEvaluation n).mapIso (sequenceHomologyComplexIso K hK q)).toLinearEquiv))

/-- 実際の自由複体列の像の Euler 評価は、各段の Euler 評価の正規化超極限と一致する。 -/
lemma supportedRankEuler_complex
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    supportedRankEuler lam hfg z hJ hfin U hU hs
      ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
        ⟨sequenceHomotopyObj K hK, hzK⟩) =
      normalizedLimit U s (fun n ↦ lambdaEuler lam ((evaluateComplex n).obj K)) := by
  unfold supportedRankEuler
  simp_rw [supportedRankHomology_length_complex lam hfg z hJ hfin U hU hs K hK hzK]
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK).mp hzK
  obtain ⟨a, b, ha, hb⟩ := hK
  symm
  apply normalizedLimit_lambdaEuler lam U hU s hs _ (Finset.Icc a b)
  · intro n q hq
    apply (FreeSequence.evaluation n).map_isZero
    simp only [Finset.mem_Icc] at hq
    by_cases hqa : q < a
    · exact K.isZero_of_isStrictlyGE a q hqa
    · exact K.isZero_of_isStrictlyLE b q (by omega)
  · intro q
    exact (complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) (hfin v hv) K ⟨a, b, ha, hb⟩ (fun n j ↦ hn j n) q).2.2

end SerrePositivity.Asymptotic

end RankEulerPart

section RankEulerAdditivityPart

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
  simp only [zsmul_eq_mul]
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

end RankEulerAdditivityPart

section RankEulerComparisonPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits Filter Asymptotics

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} {J : Ideal R} {I : Ideal S}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)

include hfg hJ hfin in
omit [Nontrivial R] in
/-- 一様に台をもつ自由複体列の Euler 値の列は `O(s)`。 -/
lemma supportedSequenceEuler_isBigO
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    (fun n ↦ lambdaEuler lam ((evaluateComplex n).obj K))
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK).mp hzK
  obtain ⟨a, b, ha, hb⟩ := hK
  apply lambdaEuler_isBigO lam s _ (Finset.Icc a b)
  · intro n q hq
    apply (FreeSequence.evaluation n).map_isZero
    simp only [Finset.mem_Icc] at hq
    by_cases hqa : q < a
    · exact K.isZero_of_isStrictlyGE a q hqa
    · exact K.isZero_of_isStrictlyLE b q (by omega)
  · intro q
    exact (complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) (hfin v hv) K ⟨a, b, ha, hb⟩ (fun n j ↦ hn j n) q).2.2

/-- 各段のテンソル積に対する比較等式は、支持つきランク商の代表複体での評価に移る。 -/
lemma supportedRankEuler_changeRing_complex
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ i,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology i) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) (c : ℝ)
    (hc : ∀ n, lambdaEuler mu (baseChange φ ((evaluateComplex n).obj K)) =
      c * lambdaEuler lam ((evaluateComplex n).obj K)) :
    supportedRankEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
      ((rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q.obj
        ⟨sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
          (changeRing_strictlyBounded φ K hK), changeRing_complex_supported φ z K hK hzK⟩) =
      c * supportedRankEuler lam hfg z hJ hfin U hU hs
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
          ⟨sequenceHomotopyObj K hK, hzK⟩) := by
  rw [supportedRankEuler_complex, supportedRankEuler_complex]
  have hn (n : ℕ) : lambdaEuler mu
      ((evaluateComplex n).obj
        (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)) =
      c * lambdaEuler lam ((evaluateComplex n).obj K) :=
    (lambdaEuler_eq_of_homotopyEquiv mu
      (HomotopyEquiv.ofIso (FreeSequence.evaluateComplexTensorIso φ n K).symm)).trans (hc n)
  simp_rw [hn]
  exact normalizedLimit_const_mul U hU s hs _
    (supportedSequenceEuler_isBigO lam hfg z hJ hfin K hK hzK) c

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 有限版の全対象の比較を、冪等完備化前の支持つきランク商の全対象に移す。 -/
lemma supportedRankEuler_changeRing
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ i,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology i) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P)
    (X : SupportedSequenceRankQuotient (s := s) z) :
    supportedRankEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
      ((supportedRankChangeRing φ z).obj X) =
      c * supportedRankEuler lam hfg z hJ hfin U hU hs X := by
  let L := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let F := supportedRankChangeRing (s := s) φ z
  have hrep (Y : (supportedSequence (s := s) z).FullSubcategory) :
      supportedRankEuler mu hIfg (φ ∘ z) hI hfinS U hU hs (F.obj (L.obj Y)) =
        c * supportedRankEuler lam hfg z hJ hfin U hU hs (L.obj Y) := by
    refine (supportedRankEuler_iso mu hIfg (φ ∘ z) hI hfinS U hU hs
      ((supportedRankChangeRingFactors φ z).app Y)).trans ?_
    obtain ⟨⟨Q, hQ⟩, hY⟩ := Y
    obtain ⟨K, rfl⟩ := Q.quotient_obj_surjective
    exact supportedRankEuler_changeRing_complex lam hfg z hJ hfin φ mu hIfg hI hfinS
      U hU hs K ((boundedHomotopyProperty_quotient _ K).mp hQ) hY c
      (fun n ↦ hc _ (evaluateComplex_isPerfectSupported z K
        ((boundedHomotopyProperty_quotient _ K).mp hQ) hY n))
  let := Localization.essSurj L
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
  exact (supportedRankEuler_iso mu hIfg (φ ∘ z) hI hfinS U hU hs
    (F.mapIso (L.objObjPreimageIso X)).symm).trans
    ((hrep (L.objPreimage X)).trans (congrArg (c * ·)
      (supportedRankEuler_iso lam hfg z hJ hfin U hU hs (L.objObjPreimageIso X))))

/-- 有限版の比較は、支持つきランク商の Grothendieck 群上でも成り立つ。 -/
lemma supportedRankEulerK0_changeRing
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ i,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology i) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P) :
    (supportedRankEulerK0 mu hIfg (φ ∘ z) hI hfinS U hU hs).comp
      (TriangulatedK0.map (supportedRankChangeRing φ z)) =
        c • supportedRankEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simpa only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, supportedRankEulerK0_mk,
    AddMonoidHom.smul_apply, smul_eq_mul] using
    supportedRankEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc X

end SerrePositivity.Asymptotic

end RankEulerComparisonPart

section CompletedEulerAdditivityPart

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
  simp only [zsmul_eq_mul]
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

end CompletedEulerAdditivityPart

section CompletedEulerComparisonPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} {J : Ideal R} {I : Ideal S}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

/-- A 側の一様代表により、Euler の階数倍公式を任意の形式的直和因子へ拡張する。 -/
theorem completedSupportedEuler_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P)
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
      (((functorExtension₂ _ _).obj (supportedRankChangeRing φ z)).obj X) =
      c * completedSupportedEuler lam hfg z hJ hfin U hU hs X := by
  let F := supportedRankChangeRing (s := s) φ z
  let E := (functorExtension₂ _ _).obj F
  obtain ⟨Y, ⟨iY⟩⟩ := Functor.EssSurj.mem_essImage
    (toKaroubi (SupportedSequenceRankQuotient (s := s) z)) X
  calc
    _ = completedSupportedEuler mu hIfg (φ ∘ z) hI hfinS U hU hs
        ((toKaroubi _).obj (F.obj Y)) :=
      completedSupportedEuler_iso _ _ _ _ _ _ _ _
        (E.mapIso iY.symm ≪≫
          ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app Y)
    _ = supportedRankEuler mu hIfg (φ ∘ z) hI hfinS U hU hs (F.obj Y) :=
      completedSupportedEuler_obj _ _ _ _ _ _ _ _ _
    _ = c * supportedRankEuler lam hfg z hJ hfin U hU hs Y :=
      supportedRankEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc Y
    _ = _ := congrArg (c * ·)
      ((completedSupportedEuler_obj lam hfg z hJ hfin U hU hs Y).symm.trans
        (completedSupportedEuler_iso lam hfg z hJ hfin U hU hs iY))

end SerrePositivity.Asymptotic

end CompletedEulerComparisonPart

section CompletedHomologyLengthPart

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

end CompletedHomologyLengthPart

section CompletedK0ComparisonPart

set_option synthInstance.maxSize 1024

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} {J : Ideal R} {I : Ideal S}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

/-- 一様自由代表を介して得た全対象の比較を、K₀ の準同型の等式へ移す。 -/
theorem completedSupportedEulerK0_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P) :
    (completedSupportedEulerK0 mu hIfg (φ ∘ z) hI hfinS U hU hs).comp
      (TriangulatedK0.map ((functorExtension₂ _ _).obj (supportedRankChangeRing φ z))) =
        c • completedSupportedEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simpa only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedSupportedEulerK0_mk, AddMonoidHom.smul_apply, smul_eq_mul] using
      completedSupportedEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc X

end SerrePositivity.Asymptotic

end CompletedK0ComparisonPart
