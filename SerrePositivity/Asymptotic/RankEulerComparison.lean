module

public import SerrePositivity.Asymptotic.RankEuler
public import SerrePositivity.Asymptotic.SequenceBaseChangeSupport
public import SerrePositivity.Asymptotic.SupportedRankBaseChange
public import SerrePositivity.Asymptotic.RankEulerAdditivity

/-!
# 代表複体上の Euler 比較をランク商へ移す

各段のテンソル積で成り立つ Euler 値の等式を正規化超極限に移す。
ここで扱うのは一様に台をもつ実際の自由複体列の像である。
商の冪等元で切り出した任意の対象への拡張には、別途持ち上げの定理が必要。
-/

@[expose] public section

universe u

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
