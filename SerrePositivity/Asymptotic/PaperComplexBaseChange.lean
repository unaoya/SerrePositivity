module

public import SerrePositivity.Asymptotic.ComplexEvaluationIndependence
public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation
public import SerrePositivity.Asymptotic.PaperTwist

/-! # 具体的な複体列による係数変更・ひねりと支持変更後の評価 -/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 論文の商と計算側の商で、同じ複体列の支持条件は一致する。 -/
lemma paperComplex_supported_iff
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) ↔
      scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) := by
  change scalarSupported z _ ↔ _
  rw [← scalarSupported_equivalence_iff (paperRankEquivalence R s) z]
  exact (scalarSupported z).prop_iff_of_iso ((paperSequenceComparison R s).app _)

/-- 行列の係数変更で得る具体的な複体列は、論文の商でも支持される。 -/
lemma paperChangedComplex_supported
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    paperSupportedRank (φ ∘ z) ((paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK))) := by
  obtain ⟨v, hv, hx⟩ := h
  apply (paperComplex_supported_iff (φ ∘ z) _ _).mpr
  exact ⟨v, hv, paperBaseChange_complex_smul_zero φ z K hK v hx⟩

/-- 抽象的な係数変更の像は、行列を係数変更した複体列の像と同型である。 -/
noncomputable def paperChangeRingComplexIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    (paperSupportedChangeRing φ z).obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ ≅
    ⟨(paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)), paperChangedComplex_supported φ z K hK h⟩ := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  let h' := paperChangedComplex_supported φ z K hK h
  let hc := (paperComplex_supported_iff (φ ∘ z) L hL).mp h'
  exact (paperSupportedRankEquivalence (φ ∘ z)).functor.preimageIso
    (paperBaseChangeComplexIso φ z K hK h hc ≪≫ (paperComplexComparison (φ ∘ z) L hL h').symm)

variable {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 係数変更の K₀ 写像と二つの支持部分圏の比較に必要。
/-- 係数変更後の Euler 評価を、別の支持の指定で同じ行列複体列上に計算できる。 -/
theorem paperBaseChangeEulerK0_complex_support_change
    {f : ℕ} (w : Fin f → S)
    (hJw : J ≤ (Ideal.span (Set.range w)).radical)
    (hfinw : ∀ v : ℕ, 0 < v → ∀ q,
      lam.len ((koszulComplex (fun j ↦ w j ^ v)).homology q) ≠ ⊤)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hw : paperSupportedRank w ((paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) =
    paperRankEulerK0 lam hfg w hJw hfinw U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor S s).obj
        (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
          (changeRing_strictlyBounded φ K hK)), hw⟩) := by
  rw [paperBaseChangeEulerK0, AddMonoidHom.comp_apply]
  rw [TriangulatedK0.map_mk,
    TriangulatedK0.mk_iso (paperChangeRingComplexIso φ z K hK h)]
  exact paperRankEulerK0_complex_support_independent lam hfg (φ ∘ z) w hJ hJw hfin hfinw
    U hU hs _ _ _ hw

/-- 恒等係数変更後の評価は、元の支持圏の評価そのものである。 -/
lemma paperBaseChangeEulerK0_id {I : Ideal R} (mu : NormalizedLength R I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range z)).radical)
    (hfinite : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤) :
    paperBaseChangeEulerK0 (RingHom.id R) z mu hIfg hI hfinite U hU hs =
      paperRankEulerK0 mu hIfg z hI hfinite U hU hs := by
  simp only [paperBaseChangeEulerK0, paperSupportedChangeRingK0_id, AddMonoidHom.comp_id]
  rfl

end SerrePositivity.Asymptotic
