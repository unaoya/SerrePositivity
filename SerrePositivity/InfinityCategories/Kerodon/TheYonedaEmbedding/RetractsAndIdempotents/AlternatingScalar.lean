module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingSimplex

/-!
概要：元の交互列の全射を、元の二元モノイドの値で比較する。
方針：同じ元の射のスカラー値を取り、非恒等冪等元と X の恒等を区別する。
規約：全 nerve 単体の等式から元の全射の値を取り、対象列だけで代用しない。
使われ方：短い交互列には潰せない元の奇数位置の検出。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の非恒等冪等元は、元の二元モノイドの恒等とは異なる。 -/
lemma walkingAbsorber_ne_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorber.{u} ≠ 1 := WithOne.coe_ne_one

/-- 元の全 nerve 単体内の指定した射の、元の二元モノイドでの値。 -/
def chainScalar {n : ℕ} (F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n)
    (i j : Fin (n + 1)) (h : i ≤ j) : WithOne PUnit.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar ((F.map (homOfLE h)).f)

/-- 元の交互セルの元の射の値は、元の頂点像間の同じ交互列の射の値。 -/
lemma alternatingCell_scalar {m n : ℕ} (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    chainScalar ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a) i j h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap (a i) (a j)).f) := rfl

/-- 元の異なる二位置の間の射の値は、同じ元の非恒等冪等元。 -/
lemma alternatingChainMap_scalar_ne {n : ℕ} (a b : Fin (n + 1)) (h : a ≠ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} a b).f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorber := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right h]
  rfl

/-- 元の奇数位置 X の恒等射の値は、同じ元の恒等元。 -/
lemma alternatingChainMap_scalar_source {n : ℕ} (a : Fin (n + 1)) (h : a.val % 2 = 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} a a).f) = 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap_self]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject a.val).p = 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingObject, ite_eq_left h]
  rfl

/-- 同じ元の全セル像を持つ単体は、元の奇数位置の逆像を共有する。 -/
lemma alternatingCell_equal_source_iff {m M n : ℕ}
    {a : (Δ[2 * m] : SSet.{u}) _⦋n⦌} {b : (Δ[2 * M] : SSet.{u}) _⦋n⦌}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M).app (Opposite.op ⦋n⦌) b) (i : Fin (n + 1)) :
    (a i).val % 2 = 1 ↔ (b i).val % 2 = 1 := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_source_iff a i, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_source_iff b i]
  exact (congrArg (fun F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n ↦ F.obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource) h).to_iff

/-- 元の全セル像を保つと、順序付きの元の奇数位置の違いは潰せない。 -/
lemma alternatingCell_equal_ordered_indices {m M n : ℕ}
    {a : (Δ[2 * m] : SSet.{u}) _⦋n⦌} {b : (Δ[2 * M] : SSet.{u}) _⦋n⦌}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M).app (Opposite.op ⦋n⦌) b)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : (b i).val % 2 = 1) (he : b i = b j) :
    a i = a j := by
  by_contra hne
  have hv := congrArg (fun F : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n ↦ chainScalar F i j hij) h
  rw [alternatingCell_scalar, alternatingCell_scalar, alternatingChainMap_scalar_ne _ _ hne,
    ← he, alternatingChainMap_scalar_source _ hi] at hv
  exact walkingAbsorber_ne_one hv

/-- 元の全セル像を保つと、元の奇数位置の違いは順序に関わらず潰せない。 -/
lemma alternatingCell_equal_indices {m M n : ℕ}
    {a : (Δ[2 * m] : SSet.{u}) _⦋n⦌} {b : (Δ[2 * M] : SSet.{u}) _⦋n⦌}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M).app (Opposite.op ⦋n⦌) b)
    (i j : Fin (n + 1)) (hi : (b i).val % 2 = 1) (he : b i = b j) : a i = a j := by
  rcases le_total i j with hij | hji
  · exact alternatingCell_equal_ordered_indices h i j hij hi he
  · have hj : (b j).val % 2 = 1 := by rw [← he]; exact hi
    exact (alternatingCell_equal_ordered_indices h j i hji hj he.symm).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
