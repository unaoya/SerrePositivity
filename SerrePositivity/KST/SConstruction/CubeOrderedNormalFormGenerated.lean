module
public import SerrePositivity.KST.SConstruction.CubeSupportOutputCompletion

/-! # 順序つき有限 max 表示からの実際の cubical 射の構成
概要：互いに順序分離した support を持つ任意の表示を、元の生成射の合成で実現する。
方針：未使用入力を削除し、全入力を尽くすブロック max の後に定数面を補完する。
規約：生成条件を仮定しない。使われ方：necklace の元の像作用を具体的 cube 圏へ送る。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 任意の順序分離した表示を圧縮すると、全入力を尽くす support 分割となる。 -/
theorem cubeOrderedNormalFormCompressedPartition {n m : ℕ} (s : CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ cubeJoinNormalFormSupport s j → l ∈ cubeJoinNormalFormSupport s k → i < l) :
    CubeSupportPartition (cubeNormalFormCompressed s) where
  ordered := by
    intro j k hjk i l hi hl
    apply (cubeNormalFormInputEmbedding s).strictMono.lt_iff_lt.mp
    exact h hjk ((mem_cubeJoinNormalFormRestrict_support s _ i j).mp hi)
      ((mem_cubeJoinNormalFormRestrict_support s _ l k).mp hl)
  covers := cubeNormalFormCompressed_no_unused s

/-- 任意の順序分離した有限 max 表示を持つ元の具体的な cubical 射。 -/
def cubeOrderedNormalFormHom {n m : ℕ} (s : CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ cubeJoinNormalFormSupport s j → l ∈ cubeJoinNormalFormSupport s k → i < l) :
    ConcreteCube.mk n ⟶ ConcreteCube.mk m :=
  cubeNormalFormInputSelection s ≫ cubeSupportMax (cubeOrderedNormalFormCompressedPartition s h) ≫
    cubeSupportOutputCompletion (cubeNormalFormCompressed s)

/-- 元の削除・ブロック max・定数面の合成は同じ表示の全頂点評価を回収する。 -/
lemma cubeOrderedNormalFormHom_eval {n m : ℕ} (s : CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ cubeJoinNormalFormSupport s j → l ∈ cubeJoinNormalFormSupport s k → i < l)
    (x : CubeVertex n) : (cubeOrderedNormalFormHom s h).val x = cubeJoinNormalFormEval s x := by
  change (cubeSupportOutputCompletion (cubeNormalFormCompressed s)).val
    ((cubeSupportMax (cubeOrderedNormalFormCompressedPartition s h)).val
      (cubeCoordinateSelect (cubeNormalFormInputEmbedding s) x)) = _
  rw [cubeSupportMax_completion_eval]
  exact cubeNormalFormCompressed_eval s x

/-- 順序分離した有限 max 表示の評価は、元の cubical 生成射から生成される。 -/
lemma cubeOrderedNormalForm_generated {n m : ℕ} (s : CubeJoinNormalForm n m)
    (h : ∀ ⦃j k : Fin m⦄, j < k → ∀ ⦃i l : Fin n⦄,
      i ∈ cubeJoinNormalFormSupport s j → l ∈ cubeJoinNormalFormSupport s k → i < l) :
    CubeMapGenerated (cubeJoinNormalFormEval s) := by
  have he : (cubeOrderedNormalFormHom s h).val = cubeJoinNormalFormEval s :=
    funext (cubeOrderedNormalFormHom_eval s h)
  rw [← he]
  exact (cubeOrderedNormalFormHom s h).property

end SerrePositivity.KST.SConstruction
