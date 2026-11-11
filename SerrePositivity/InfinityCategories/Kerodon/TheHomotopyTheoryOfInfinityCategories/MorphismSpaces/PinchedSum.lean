module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSecond
public import Mathlib.Algebra.BigOperators.Option

/-! # 右 pinched 方程式の有限和の添字

概要：最終点を加えた集合の和を、最終点の項と先頭集合の和に分ける。
方針：追加した最終点を Option の none、先頭点を some で表す同値を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：方程式の右辺の線形化。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最終点を加えた集合の点は、先頭集合の点または追加した最終点と同値。
方針：none を最終点、some を先頭埋め込みに送り、二つの場合で全単射を示す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：所属証明を持つ和の添字の交換。 -/
def withLastEquiv {n : ℕ} (J : Finset (Fin (n + 1))) : Option J ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J :=
  Equiv.ofBijective (fun t => match t with
    | none => ⟨Fin.last (n + 1), Finset.mem_insert_self _ _⟩
    | some j => ⟨j.val.castSucc,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, j.property, rfl⟩)⟩) (by
    constructor
    · intro a b hab
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          exact False.elim ((ne_of_gt (Fin.castSucc_lt_last b.val)) (congrArg Subtype.val hab))
      | some a =>
        cases b with
        | none =>
          exact False.elim ((ne_of_lt (Fin.castSucc_lt_last a.val)) (congrArg Subtype.val hab))
        | some b =>
          congr 1
          apply Subtype.ext
          exact (Fin.castSucc_injective _) (congrArg Subtype.val hab)
    · rintro ⟨i, hi⟩
      induction i using Fin.lastCases with
      | last => exact ⟨none, rfl⟩
      | cast i =>
        have hj : i ∈ J := by simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast] using hi
        exact ⟨some ⟨i, hj⟩, rfl⟩)

/-- 概要：追加した最終点の和を先頭集合の和から分離する。
方針：Option との同値で和を移し、none と some に分ける。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右辺の最終点の零項の消去。 -/
lemma sum_withLast {n : ℕ} {M : Type*} [AddCommMonoid M] (J : Finset (Fin (n + 1)))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J → M) :
    ∑ i : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J, f i =
      f ⟨Fin.last (n + 1), Finset.mem_insert_self _ _⟩ +
        ∑ j : J, f ⟨j.val.castSucc,
          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, j.property, rfl⟩)⟩ := by
  rw [← Fintype.sum_equiv (withLastEquiv J) (fun t => f (withLastEquiv J t)) f (fun _ => rfl)]
  exact Fintype.sum_option _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
