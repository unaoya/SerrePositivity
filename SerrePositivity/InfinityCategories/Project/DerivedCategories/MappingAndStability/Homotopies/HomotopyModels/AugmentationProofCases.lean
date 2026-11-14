module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # augmentation の共通する場合分け

一般 comma と semifree 加群の二系統で重複していた Prop の証明を共有する。
データの候補やその係数は引数に現れず、既存の構成本体を変更しない。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 単調な二相の両端は同相か零から一への混合相であり、それぞれで命題を確認すればよい。 -/
lemma augmentation_proof_of_endpoint_phases {n : ℕ}
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    {Q : Prop} (hsame : ∀ p : Fin 2, β a = p → β b = p → Q)
    (hmixed : β a = 0 → β b = 1 → Q) : Q := by
  have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
  rcases hp (β a) with ha0 | ha1
  · rcases hp (β b) with hb0 | hb1
    · exact hsame 0 ha0 hb0
    · exact hmixed ha0 hb1
  · rcases hp (β b) with hb0 | hb1
    · have hab : a ≤ b := by
        rw [ha, hb]
        exact (I.isLeast_min' _).2 (I.max'_mem _)
      have hh := β.monotone hab
      rw [ha1, hb0] at hh
      change (1 : ℕ) ≤ 0 at hh
      omega
    · exact hsame 1 ha1 hb1

/-- 有限添字上の単射、潰れた二点、残る非単射の場合の命題を一つにまとめる。 -/
lemma augmentation_proof_of_reindex_cases {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    {Q : Prop} (hinj : Set.InjOn α (I : Set (Fin (m + 1))) → Q)
    (hpair : ¬ Set.InjOn α (I : Set (Fin (m + 1))) → I.card = 2 → Q)
    (hhigh : ¬ Set.InjOn α (I : Set (Fin (m + 1))) → I.card ≠ 2 → Q) : Q := by
  by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
  · exact hinj hi
  · by_cases hc : I.card = 2
    · exact hpair hi hc
    · exact hhigh hi hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
