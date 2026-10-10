module

public import SerrePositivity.CategoryTheory.TruncationTriangle
public import SerrePositivity.Asymptotic.PaperRankEvaluation

/-! # 小さいランクの尾部を切り捨てる比較

切り捨てる各項のランクが `o(s)` なら、切り詰めの包含はランク商で同型になる。
したがって、計算に必要な次数まで切り詰めを深くしても、支持つき K₀ 類は変わらない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits Asymptotics Filter StupidTruncation

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

/-- 切り捨てる範囲の各項が小さいなら、尾部全体が小さいランクの有界複体である。 -/
lemma below_rankSmall (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    rankSmallComplex (below K (a - 1)) := by
  refine ⟨below_bounded K hK (a - 1), fun q ↦ ?_⟩
  by_cases hq : q ≤ a - 1
  · simpa only [FreeSequence.rank_eq_of_iso (belowXIso K (a - 1) q hq)] using
      hsmall q (by omega)
  · simp only [FreeSequence.rank_eq_zero_of_isZero _
      (below_isZero_X K (a - 1) q (by omega)), Nat.cast_zero]
    exact isLittleO_zero _ _

/-- 小さいランクの尾部を切る包含は、論文のランク商で同型になる。 -/
lemma paper_inclusion_isIso (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    IsIso ((paperSequenceFunctor R s).map (boundedInclusion K hK a)) := by
  apply isIso_map_boundedInclusion (paperSequenceFunctor R s) K hK a
  apply karoubiFirstFromOriginal_kills
  exact ⟨(HomotopyCategory.quotient _ _).obj (below K (a - 1)),
    (rankSmallHomotopy_quotient _).mpr (below_rankSmall K hK a hsmall), ⟨Iso.refl _⟩⟩

/-- 切り詰めを変えても、ランク商の対象は同型である。 -/
noncomputable def paperTruncationIso (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    (paperSequenceFunctor R s).obj (sequenceHomotopyObj (above K a) (above_bounded K hK a)) ≅
      (paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK) := by
  have := paper_inclusion_isIso K hK a hsmall
  exact asIso ((paperSequenceFunctor R s).map (boundedInclusion K hK a))

/-- 支持つき K₀ の類も変わらず、任意の Euler 評価に使える。 -/
lemma paperTruncation_K0_eq {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)))
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    TriangulatedK0.mk
      (⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj (above K a) (above_bounded K hK a)),
        (scalarSupported z).prop_of_iso (paperTruncationIso K hK a hsmall).symm h⟩ :
        (paperSupportedRank (s := s) z).FullSubcategory) =
      TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ := by
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (paperTruncationIso K hK a hsmall))

end SerrePositivity.Asymptotic
