module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedIndex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index

/-! # 右 pinched 引き戻しの有限集合の添字

概要：最終点固定の延長が終端を含む集合の像と単射性を保つ形を記述する。
方針：先頭点と最終点を分け、元の先頭集合上の写像へ帰着する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：回収と線形引き戻しの自然性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最終点固定延長による終端集合の像は、元の像に最終点を加えた集合。
方針：最終点の像と先頭埋め込みとの可換性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：引き戻しの単射分岐の成分。 -/
lemma image_withLast_extend {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (J.image α) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, Finset.image_insert, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last,
    Finset.image_image]
  apply congrArg (insert (Fin.last (n + 1)))
  apply congrArg (fun f => J.image f)
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α i

/-- 概要：延長写像が終端集合上で単射であることと元の写像が先頭集合上で単射であることは同値。
方針：先頭点と最終点の像が混ざらないことを使い、先頭同士だけで元の単射性を検査する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：引き戻しの単射・零の分岐の一致。 -/
lemma injOn_extend_withLast_iff {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) :
    Set.InjOn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J : Set (Fin (m + 2))) ↔ Set.InjOn α (J : Set (Fin (m + 1))) := by
  constructor
  · intro hi a ha b hb hab
    apply Fin.castSucc_injective (m + 1)
    apply hi (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, hab]
  · intro hi a ha b hb hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b =>
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] at hab
        exact False.elim ((ne_of_gt (Fin.castSucc_lt_last (α b))) hab)
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] at hab
        exact False.elim ((ne_of_lt (Fin.castSucc_lt_last (α a))) hab)
      | cast b =>
        have haJ : a ∈ J := by simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast] using ha
        have hbJ : b ∈ J := by simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast] using hb
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] at hab
        exact congrArg Fin.castSucc (hi haJ hbJ ((Fin.castSucc_injective _) hab))

/-- 概要：非単射な有限集合は二点以上を持つ。
方針：濃度一以下では所属する二点が一致することを使う。
規約：HA Construction 1.3.1.6。使われ方：延長して潰れる成分が二点の単位分岐にならないこと。 -/
lemma two_of_not_injOn {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (hi : ¬ Set.InjOn α (J : Set (Fin (m + 1)))) :
    2 ≤ J.card := by
  by_contra h
  apply hi
  intro a ha b hb _
  exact (Finset.card_le_one.mp (show J.card ≤ 1 by omega)) a ha b hb

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
