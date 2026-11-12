module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
public import Mathlib.Data.Finset.Preimage
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-! # ホーンから回収できる部分集合

概要：全体集合と欠けた面以外の部分集合は、ホーンの利用可能な面に含まれる。
方針：補集合に欠けた面の番号以外の点を見つけ、面の順序埋め込みの逆像で添字を移す。
規約：HA Proposition 1.3.1.10。使われ方：ホーンの面から斉次成分を回収する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：利用可能な面に含まれる部分集合は、全体集合と欠けた面を除いたものに一致する。
方針：欠けた面番号以外を全て含むなら、その番号の所属に応じて例外の二集合のいずれかになる。
規約：HA Proposition 1.3.1.10。使われ方：既知成分を持つ面の存在証明。 -/
lemma exists_covering_face {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α) (i : α) :
    (∃ j, j ≠ i ∧ j ∉ I) ↔ I ≠ Finset.univ ∧ I ≠ Finset.univ.erase i := by
  constructor
  · rintro ⟨j, hji, hj⟩
    constructor
    · intro h
      exact hj (h ▸ Finset.mem_univ j)
    · intro h
      exact hj (h ▸ Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  · rintro ⟨hfull, hmissing⟩
    by_contra h
    push Not at h
    by_cases hi : i ∈ I
    · apply hfull
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      by_cases hji : j = i
      · simpa only [hji] using hi
      · exact h j hji
    · apply hmissing
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hj he => hi (he ▸ hj), fun hj => h j hj⟩

/-- 概要：既知の部分集合を含むホーンの面を一つ選ぶ。
方針：面の存在補題から選択する。
規約：HA Proposition 1.3.1.10。使われ方：斉次成分を評価する面の選択。 -/
def coveringFace {n : ℕ} (I : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) : Fin (n + 1) :=
  ((exists_covering_face I i).mpr ⟨hfull, hmissing⟩).choose

/-- 概要：選んだ面は欠けた面ではない。
方針：選択の仕様を取り出す。
規約：HA Proposition 1.3.1.10。使われ方：`horn.face` の番号の条件。 -/
lemma coveringFace_ne {n : ℕ} (I : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) :
    coveringFace I i hfull hmissing ≠ i :=
  ((exists_covering_face I i).mpr ⟨hfull, hmissing⟩).choose_spec.1

/-- 概要：選んだ面で飛ばす頂点は部分集合に含まれない。
方針：選択の仕様を取り出す。
規約：HA Proposition 1.3.1.10。使われ方：部分集合の面への引き戻し。 -/
lemma coveringFace_notMem {n : ℕ} (I : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) :
    coveringFace I i hfull hmissing ∉ I :=
  ((exists_covering_face I i).mpr ⟨hfull, hmissing⟩).choose_spec.2

/-- 概要：飛ばす頂点を含まない集合は、面の順序埋め込みの逆像の像として復元できる。
方針：面の埋め込みの値域は飛ばした頂点の補集合である。
規約：HA Proposition 1.3.1.10。使われ方：面上の成分の添字の復元。 -/
lemma image_preimage {n : ℕ} (I : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ I) :
    (I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn).image j.succAbove = I := by
  rw [Finset.image_preimage j.succAbove I]
  apply Finset.filter_eq_self.mpr
  intro x hx
  exact Fin.exists_succAbove_eq (fun h => hj (h ▸ hx))

/-- 概要：面へ引き戻した部分集合の濃度は元の集合と等しい。
方針：像での復元と面の埋め込みの単射性を使う。
規約：HA Proposition 1.3.1.10。使われ方：斉次成分の次数の移送。 -/
lemma card_preimage {n : ℕ} (I : Finset (Fin (n + 2))) (j : Fin (n + 2)) (hj : j ∉ I) :
    (I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn).card = I.card := by
  have h := Finset.card_image_of_injOn (f := j.succAbove)
    (s := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn)
    j.succAboveOrderEmb.injective.injOn
  rw [image_preimage I j hj] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
