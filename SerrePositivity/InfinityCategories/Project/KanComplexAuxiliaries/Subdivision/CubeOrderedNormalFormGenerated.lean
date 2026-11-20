module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeSupportOutputCompletion

/-! # 順序つき有限 max 表示からの実際の cubical 射の構成
概要：互いに順序分離した support を持つ任意の表示を、元の生成射の合成で実現する。
方針：未使用入力を削除し、全入力を尽くすブロック max の後に定数面を補完する。
規約：生成条件を仮定しない。使われ方：necklace の元の像作用を具体的 cube 圏へ送る。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 任意の順序分離した表示を圧縮すると、全入力を尽くす support 分割となる。 -/
theorem cubeOrderedNormalFormCompressedPartition {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s) where
  ordered := by
    intro j k hjk i l hi hl
    apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).strictMono.lt_iff_lt.mp
    exact h hjk ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormRestrict_support s _ i j).mp hi)
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_cubeJoinNormalFormRestrict_support s _ l k).mp hl)
  covers := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_no_unused s

/-- 任意の順序分離した有限 max 表示を持つ元の具体的な cubical 射。 -/
def cubeOrderedNormalFormHom {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection s ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormCompressedPartition s h) ≫
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s)

/-- 元の削除・ブロック max・定数面の合成は同じ表示の全頂点評価を回収する。 -/
lemma cubeOrderedNormalFormHom_eval {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k → i < l)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormHom s h).val x = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s x := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s)).val
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormCompressedPartition s h)).val
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s) x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax_completion_eval]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval s x

/-- 順序分離した有限 max 表示の評価は、元の cubical 生成射から生成される。 -/
lemma cubeOrderedNormalForm_generated {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormHom s h).val = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s :=
    funext (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormHom_eval s h)
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalFormHom s h).property

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
