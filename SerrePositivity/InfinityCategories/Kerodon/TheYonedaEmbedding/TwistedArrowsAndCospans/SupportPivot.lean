module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseExtensionDomain

/-!
概要：twisted arrow の左ホーンの延長領域と、欠ける頂点集合の内部の挿入点。
方針：左右の半分と、欠ける面以外の対応する二頂点を除いた面を延長領域とする。
規約：ホーンの番号は最後以外。挿入点が端点にならないことを実際の頂点で証明する。
使われ方：twisted arrow 射影の left fibration 性を示す inner horn の pairing。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 左右の半分または欠ける面以外の一対を避ける頂点集合が、延長領域に属する。 -/
def TwistedArrowSupportInDomain {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) : Prop :=
  (∀ v ∈ S, v.val ≤ n) ∨ (∀ v ∈ S, n < v.val) ∨
    ∃ j : Fin (n + 1), j ≠ i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ∉ S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j ∉ S

/-- 領域外の集合は左右の頂点を含み、指定された全ての対に交わる。 -/
lemma not_twistedArrowSupportInDomain_iff {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) :
    ¬ TwistedArrowSupportInDomain i S ↔
      (∃ a ∈ S, a.val ≤ n) ∧ (∃ b ∈ S, n < b.val) ∧
        ∀ j : Fin (n + 1), j ≠ i → _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ∈ S ∨
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j ∈ S := by
  classical
  simp only [TwistedArrowSupportInDomain, not_or, not_forall, not_exists, not_and,
    not_not, not_le, not_lt]
  constructor
  · rintro ⟨⟨b, hb, hb'⟩, ⟨a, ha, ha'⟩, h⟩
    refine ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, fun j hj ↦ ?_⟩
    by_cases hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ∈ S
    · exact Or.inl hl
    · exact Or.inr (h j hj hl)
  · rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, h⟩
    exact ⟨⟨b, hb, hb'⟩, ⟨a, ha, ha'⟩, fun j hj hl ↦ (h j hj).resolve_left hl⟩

/-- 指定番号より大きい添字の左頂点を含むという、挿入点の分岐条件。 -/
def TwistedArrowHasUpperLeft {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) : Prop :=
  ∃ j : Fin (n + 1), i < j ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ∈ S

/-- 領域外の集合の pairing は、指定番号の左または右の頂点を挿入する。 -/
def twistedArrowSupportPivot {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) : Fin (n + n + 1 + 1) := by
  classical
  exact if TwistedArrowHasUpperLeft i S then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i
    else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i

/-- 左ホーンでは、選んだ挿入点の前後に既存の頂点が必ず存在する。 -/
lemma twistedArrowSupportPivot_interior {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (S : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ TwistedArrowSupportInDomain i S) :
    ∃ a ∈ S, ∃ b ∈ S, a < twistedArrowSupportPivot i S ∧
      twistedArrowSupportPivot i S < b := by
  classical
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, hp⟩ :=
    (not_twistedArrowSupportInDomain_iff i S).mp hS
  by_cases h : TwistedArrowHasUpperLeft i S
  · have hchoice : twistedArrowSupportPivot i S = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i := by
      simp only [twistedArrowSupportPivot, ite_eq_left h]
    obtain ⟨j, hj, hjS⟩ := h
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j, hjS, b, hb, ?_, ?_⟩
    · simp only [hchoice, Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex]
      have := j.isLt
      change i.val < j.val at hj
      omega
    · simp only [hchoice, Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex]
      omega
  · have hni : Fin.last n ≠ i := ne_of_gt hi
    have hnL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n (Fin.last n) ∉ S := by
      intro hn
      exact h ⟨Fin.last n, hi, hn⟩
    have hnR := (hp (Fin.last n) hni).resolve_left hnL
    refine ⟨a, ha, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (Fin.last n), hnR, ?_, ?_⟩
    · simp only [twistedArrowSupportPivot, ite_eq_right h, Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex]
      omega
    · simp only [twistedArrowSupportPivot, ite_eq_right h, Fin.lt_def, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex,
        Fin.val_last]
      change i.val < (Fin.last n).val at hi
      simp only [Fin.val_last] at hi
      omega

/-- 指定番号以外の左頂点は、選んだ挿入点とは異なる。 -/
lemma twistedArrowSupportPivot_ne_left {n : ℕ} (i j : Fin (n + 1))
    (hji : j ≠ i) (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n j ≠ twistedArrowSupportPivot i S := by
  classical
  unfold twistedArrowSupportPivot
  split_ifs
  · intro h
    apply hji
    apply Fin.ext
    have hh := congrArg Fin.val h
    have := i.isLt
    have := j.isLt
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex] at hh
    omega
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n j i

/-- 指定番号以外の右頂点も、選んだ挿入点とは異なる。 -/
lemma twistedArrowSupportPivot_ne_right {n : ℕ} (i j : Fin (n + 1))
    (hji : j ≠ i) (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n j ≠ twistedArrowSupportPivot i S := by
  classical
  unfold twistedArrowSupportPivot
  split_ifs
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n i j).symm
  · intro h
    apply hji
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex] at hh
    omega

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
