module

public import SerrePositivity.Asymptotic.PaperRankQuotient

/-! # 論文の圏上のホモロジー評価と K₀ -/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 論文の支持部分圏から長さの Serre 商への第 q 次ホモロジー関手。 -/
noncomputable abbrev paperRankHomology (q : ℤ) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  (paperSupportedRankEquivalence z).functor ⋙ completedRankHomology lam hfg z hJ hfin U hU hs q

instance paperRankHomology_isHomological (q : ℤ) :
    (paperRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by infer_instance

/-- 論文の支持対象の非負なホモロジー長。 -/
noncomputable abbrev paperRankBetti
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  completedRankBetti lam hfg z hJ hfin U hU hs ((paperSupportedRankEquivalence z).functor.obj X) q

lemma paperRankBetti_nonneg (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ paperRankBetti lam hfg z hJ hfin U hU hs X q := completedRankBetti_nonneg ..

lemma paperRankBetti_hasFiniteSupport (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (paperRankBetti lam hfg z hJ hfin U hU hs X) :=
  completedRankBetti_hasFiniteSupport ..

/-- 論文の圏の K₀ 上に定義された Euler 評価。 -/
noncomputable def paperRankEulerK0 :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+ ℝ :=
  (completedRankEulerK0 lam hfg z hJ hfin U hU hs).comp
    (TriangulatedK0.map (paperSupportedRankEquivalence z).functor)

lemma paperRankEulerK0_mk (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    paperRankEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * paperRankBetti lam hfg z hJ hfin U hU hs X q := by
  rw [paperRankEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedRankEulerK0_mk]
  rfl

/-- 同じ複体列の論文側と計算側の像を、支持部分圏の中で比較する。 -/
noncomputable def paperComplexComparison
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    (paperSupportedRankEquivalence z).functor.obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ ≅
        completedComplexObj z K hK
          ((scalarSupported z).prop_of_iso ((paperSequenceComparison R s).app _)
            (scalarSupported_map z (paperRankEquivalence R s).functor _ h)) :=
  ObjectProperty.isoMk _ ((paperSequenceComparison R s).app _)

set_option maxHeartbeats 800000 in
-- 支持部分圏と圏同値を含む型の比較に必要。
/-- 論文と同じ圏で述べた公式 (4.2) の係数等式。 -/
theorem paperRankBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex n).obj K)).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperRankBetti lam hfg z hJ hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  let E := paperRankEquivalence R s
  let iK := (paperSequenceComparison R s).app (sequenceHomotopyObj K hK)
  have hx' : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0 := by
    intro j
    have he : z j ^ v • 𝟙 (E.functor.obj ((paperSequenceFunctor R s).obj
        (sequenceHomotopyObj K hK))) = 0 := by
      simpa only [Functor.map_smul, E.functor.map_id, E.functor.map_zero] using
        E.functor.congr_map (hx j)
    apply (cancel_epi iK.hom).mp
    simp only [comp_zero, Linear.comp_smul, Category.comp_id] at he ⊢
    simpa using he =≫ iK.hom
  let h' : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) :=
    (scalarSupported z).prop_of_iso iK (scalarSupported_map z E.functor _ h)
  refine (completedRankBetti_koszul_formula z lam hfg hJ hfin U hU hs K hK h' v hv hx' i).trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact (completedRankBetti_iso lam hfg z hJ hfin U hU hs
    (paperComplexComparison z K hK h) _).symm

end SerrePositivity.Asymptotic
