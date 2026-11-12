module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitCard
public import Mathlib.Order.Hom.Set

/-! # 元の左右フィルターの局所頂点ブロック
概要：元の左右部分集合の包含を、元の局所頂点の始端・終端ブロックと同定する。
方針：元の像と濃度から、同じ有限順序の厳密単調写像の一意性を使う。
規約：共有頂点を左右に含む。使われ方：元の分割 augmentation と二 bead の貼り合わせ。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の左部分集合の昇順包含は、同じ局所番号を保持する。 -/
lemma simplexSubsetSplitLeft_block {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (v : Fin ((I.filter (· ≤ j)).card - 1 + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (· ≤ j)) I hL hI
      (Finset.filter_subset _ _) v).val = v.val := by
  let k := simplexSubsetVertexIndex I hI j hj
  have hc := simplexSubsetSplitLeft_card I hI j hj hL
  have hk := k.isLt
  let f : Fin ((I.filter (· ≤ j)).card - 1 + 1) → Fin (I.card - 1 + 1) :=
    fun w => ⟨w.val, by have hw := w.isLt; dsimp [k] at hk; omega⟩
  have hf : StrictMono f := by intro a b hab; exact hab
  have hr : Set.range f = Set.Iic k := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      change a.val ≤ k.val
      have ha := a.isLt
      change (I.filter (· ≤ j)).card = k.val + 1 at hc
      omega
    · intro hw
      change w.val ≤ k.val at hw
      change (I.filter (· ≤ j)).card = k.val + 1 at hc
      refine ⟨⟨w.val, by omega⟩, ?_⟩
      exact Fin.ext rfl
  have hi := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (· ≤ j)) I hL hI
    (Finset.filter_subset _ _)).monotone.strictMono_of_injective
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_injective _ _ hL hI (Finset.filter_subset _ _))
  have he := hi.eq_of_range_eq hf ((simplexSubsetSplitLeft_range I hI j hj hL).trans hr.symm)
  exact congrArg (fun g => (g v).val) he

/-- 元の右部分集合の昇順包含は、元の切断局所番号を加える。 -/
lemma simplexSubsetSplitRight_block {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hR : 2 ≤ (I.filter (j ≤ ·)).card)
    (v : Fin ((I.filter (j ≤ ·)).card - 1 + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (j ≤ ·)) I hR hI
      (Finset.filter_subset _ _) v).val =
      (simplexSubsetVertexIndex I hI j hj).val + v.val := by
  let k := simplexSubsetVertexIndex I hI j hj
  have hc := simplexSubsetSplitRight_card I hI j hj hR
  have hk := k.isLt
  let f : Fin ((I.filter (j ≤ ·)).card - 1 + 1) → Fin (I.card - 1 + 1) :=
    fun w => ⟨k.val + w.val, by have hw := w.isLt; omega⟩
  have hf : StrictMono f := by
    intro a b hab
    change k.val + a.val < k.val + b.val
    exact Nat.add_lt_add_left hab _
  have hr : Set.range f = Set.Ici k := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      change k.val ≤ k.val + a.val
      omega
    · intro hw
      change k.val ≤ w.val at hw
      have hw' := w.isLt
      refine ⟨⟨w.val - k.val, by omega⟩, ?_⟩
      apply Fin.ext
      change k.val + (w.val - k.val) = w.val
      omega
  have hi := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (j ≤ ·)) I hR hI
    (Finset.filter_subset _ _)).monotone.strictMono_of_injective
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_injective _ _ hR hI (Finset.filter_subset _ _))
  have he := hi.eq_of_range_eq hf ((simplexSubsetSplitRight_range I hI j hj hR).trans hr.symm)
  exact congrArg (fun g => (g v).val) he

end SerrePositivity.KST.SConstruction
