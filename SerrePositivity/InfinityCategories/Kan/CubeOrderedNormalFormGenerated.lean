module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeSupportOutputCompletion

/-! # 順序つき有限 max 表示からの実際の cubical 射の構成
概要：互いに順序分離した support を持つ任意の表示を、元の生成射の合成で実現する。
方針：未使用入力を削除し、全入力を尽くすブロック max の後に定数面を補完する。
規約：生成条件を仮定しない。使われ方：necklace の元の像作用を具体的 cube 圏へ送る。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 任意の順序分離した表示を圧縮すると、全入力を尽くす support 分割となる。 -/
theorem cubeOrderedNormalFormCompressedPartition {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed s) where
  _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition.ordered := by
    intro j k hjk i l hi hl
    apply (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s).strictMono.lt_iff_lt.mp
    exact h hjk ((_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormRestrict_support s _ i j).mp hi)
      ((_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeJoinNormalFormRestrict_support s _ l k).mp hl)
  _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition.covers := _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed_no_unused s

/-- 任意の順序分離した有限 max 表示を持つ元の具体的な cubical 射。 -/
def cubeOrderedNormalFormHom {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk m :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputSelection s ≫ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormCompressedPartition s h) ≫
    _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed s)

/-- 元の削除・ブロック max・定数面の合成は同じ表示の全頂点評価を回収する。 -/
lemma cubeOrderedNormalFormHom_eval {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s k → i < l)
    (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) : (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom s h).val x = _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x := by
  change (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed s)).val
    ((_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormCompressedPartition s h)).val
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputEmbedding s) x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_completion_eval]
  exact _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormCompressed_eval s x

/-- 順序分離した有限 max 表示の評価は、元の cubical 生成射から生成される。 -/
lemma cubeOrderedNormalForm_generated {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j → l ∈ _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s k → i < l) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s) := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom s h).val = _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s :=
    funext (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom_eval s h)
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom s h).property

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeOrderedNormalFormCompressedPartition := _root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormCompressedPartition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeOrderedNormalFormHom := _root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeOrderedNormalFormHom_eval := _root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalFormHom_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeOrderedNormalForm_generated := _root_.SerrePositivity.InfinityCategories.Kan.cubeOrderedNormalForm_generated
