module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakImage

/-!
概要：元の交互列の長さを増やしても、元の全前半部分と最初の分裂三角形を保持する。
方針：元の標準単体の先頭部分への包含を使い、全射の元の式を比較する。
規約：元の全 nerve 単体を等式で照合し、対象列だけの比較では代用しない。
使われ方：元の Ret 濾過の単調性と Ret(1) の同定。

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

/-- 元の交互列の全射は、長さを増やしても元の先頭部分では厳密に同じ。 -/
lemma alternatingChainMap_castLE {n N : ℕ} (h : n ≤ N) (a b : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap.{u} (a.castLE (Nat.succ_le_succ h)) (b.castLE (Nat.succ_le_succ h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap a b := by
  by_cases hab : a = b
  · subst b
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap_self]
    rfl
  have hab' : a.castLE (Nat.succ_le_succ h) ≠ b.castLE (Nat.succ_le_succ h) := by
    intro he
    exact hab (Fin.castLE_injective _ he)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChainMap, dite_eq_right hab, dite_eq_right hab']
  rfl

/-- 元の小さい標準単体を元の大きい標準単体の先頭部分へ入れる順序射。 -/
def alternatingPrefix {n N : ℕ} (h : n ≤ N) : ⦋n⦌ ⟶ ⦋N⦌ :=
  SimplexCategory.Hom.mk (Fin.castLEOrderEmb (Nat.succ_le_succ h)).toOrderHom

/-- 元の交互列の先頭部分への制限は、元の小さい交互列の全単体そのもの。 -/
lemma alternatingCell_prefix {m M : ℕ} (h : m ≤ M) :
    SSet.stdSimplex.map (alternatingPrefix (Nat.mul_le_mul_left 2 h)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} M =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape]
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  change (SimplexCategory.toCat.map
    (alternatingPrefix (Nat.mul_le_mul_left 2 h))).toFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain (2 * M) = _
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact alternatingChainMap_castLE (Nat.mul_le_mul_left 2 h) a b

/-- 最初の元の交互列は、元の包含・射影の同じ分裂二単体。 -/
lemma alternatingChain_two : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingChain.{u} 2 =
    ComposableArrows.mk₂ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction := by
  refine CategoryTheory.Functor.ext (fun i ↦ by fin_cases i <;> rfl) ?_
  intro a b f
  fin_cases a <;> fin_cases b
  all_goals try { have h := leOfHom f; simp at h }
  all_goals apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  all_goals rfl

/-- 元の Ret(1) のセルは、保存済みの元の分裂二単体そのもの。 -/
lemma alternatingCell_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle]
  exact congrArg SSet.yonedaEquiv.symm alternatingChain_two

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
