module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SupportPairing
public import Mathlib.Order.RelClasses

/-!
概要：twisted arrow の内部点の pairing に対し、別の対への面関係で減少する順位を与える。
方針：左挿入の分岐を右挿入より後に置き、同じ分岐では頂点数で順位を付ける。
規約：ここでは有限頂点集合の面関係を扱い、単体的 pairing への移送は別工程。
使われ方：inner horn の接合の正則性と停止性。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 頂点集合の包含は、上側の左頂点を持つ条件を保つ。 -/
lemma twistedArrowHasUpperLeft_mono {n : ℕ} (i : Fin (n + 1))
    {S T : Finset (Fin (n + n + 1 + 1))} (hST : S ⊆ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S → _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i T := by
  rintro ⟨j, hj, hS⟩
  exact ⟨j, hj, hST hS⟩

/-- 祖先となる頂点集合には、分岐と頂点数の辞書式順位が付く。 -/
def twistedArrowSupportRank {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) : ℕ × ℕ := by
  classical
  exact (if _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S then 1 else 0, S.card)

/-- 別の対の大きい集合の面となる小さい集合は、辞書式順位が厳密に下がる。 -/
lemma twistedArrowSupportRank_lt {n : ℕ} (i : Fin (n + 1))
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hST : S ⊆ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i T) T)
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S ∉ S) (hne : S ≠ T) :
    Prod.Lex (· < ·) (· < ·) (twistedArrowSupportRank i S)
      (twistedArrowSupportRank i T) := by
  classical
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S → _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i T := fun h ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHasUpperLeft_insert_pivot_iff i T).mp
      (twistedArrowHasUpperLeft_mono i hST h)
  have hc (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i T) :
      S.card < T.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun v hv ↦ ?_, hne⟩
    rcases Finset.mem_insert.mp (hST hv) with h | h
    · exact False.elim (hS (by simpa only [h, hp] using hv))
    · exact h
  by_cases hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S
  · have ht := hb hs
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i T := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot, ite_eq_left hs, ite_eq_left ht]
    simpa only [twistedArrowSupportRank, ite_eq_left hs, ite_eq_left ht] using
      (Prod.Lex.right 1 (hc hp))
  · by_cases ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i T
    · simp only [twistedArrowSupportRank, ite_eq_right hs, ite_eq_left ht]
      exact Prod.Lex.left _ _ (by omega)
    · have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i T := by
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot, ite_eq_right hs, ite_eq_right ht]
      simpa only [twistedArrowSupportRank, ite_eq_right hs, ite_eq_right ht] using
        (Prod.Lex.right 0 (hc hp))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
