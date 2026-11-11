module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EZUniversalDifference
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairFaceSum

/-!
# 比較の普遍な差の境界

概要：恒等と AW→shuffle の差は交代面移送と微分に関して同じ境界を持つ。
方針：普遍作用素の単射性と実比較の鎖写像性を使う。
規約：KST Construction A.5、零次の差は実計算で零にする。
使われ方：標準比較ホモトピーの再帰を始め、充填入力のサイクル性を得る。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：恒等と実 AW→shuffle の差は微分と可換。
方針：実鎖写像の差の微分可換性を評価する。
規約：KST A.5。使われ方：普遍な差の境界を検出する。 -/
lemma ezDifference_comm (C D : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) :
    (𝟙 _ - alexanderWhitneyApp C D (n + 1) ≫ shuffleApp C D (n + 1)) ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n =
    ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n ≫
      (𝟙 _ - alexanderWhitneyApp C D n ≫ shuffleApp C D n) :=
  (𝟙 _ - alexanderWhitney C D ≫ shuffle C D).comm (n + 1) n

/-- 概要：普遍な差の鎖の境界は一つ低い差の全ての面への交代移送。
方針：普遍模型自身の作用素で検出し、実鎖写像の微分可換性へ帰着する。
規約：KST Construction A.5、追加の比較存在仮定を置かない。
使われ方：再帰のサイクル性の主等式。 -/
lemma ezUniversalDifference_boundary (n : ℕ) :
    ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel.{u} (n + 1)))).d
      (n + 1) n (ezUniversalDifference (n + 1)) =
    simplexPairFaceSum (op ⦋n⦌) (ezUniversalDifference n) := by
  apply simplexPairOperation_injective (n + 1) (op ⦋n⦌)
  rw [simplexPairOperation_boundary, simplexPairOperation_ezDifference,
    simplexPairOperation_faceSum, simplexPairOperation_ezDifference]
  exact ezDifference_comm _ _ n

/-- 概要：零次で AW の後の shuffle は恒等。
方針：唯一の切断と空の格子路を実写像の有限和へ評価する。
規約：KST A.5、非被約零次を含む。
使われ方：普遍比較ホモトピーの零次の始点。 -/
lemma ezComposite_zero (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    alexanderWhitneyApp C D 0 ≫ shuffleApp C D 0 = 𝟙 _ := by
  letI : Unique (ShuffleIndex 0 0) :=
    { default := ⟨∅, by simp⟩
      uniq := fun s ↦ by
        apply Subtype.ext
        apply Finset.ext
        intro a
        exact Fin.elim0 a }
  have hf (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := by
    apply SimplexCategory.Hom.ext
    ext j
    have hj : (j : ℕ) < 1 := j.isLt
    have hk : (f.toOrderHom j : ℕ) < 1 := (f.toOrderHom j).isLt
    change (f.toOrderHom j : ℕ) = (j : ℕ)
    omega
  rw [alexanderWhitneyApp, Fin.sum_univ_one, alexanderWhitneySummand,
    Category.assoc, ι_shuffleApp, shuffleBidegree]
  simp only [Fin.val_zero]
  rw [Fintype.sum_unique]
  have hi : (default : ShuffleIndex 0 0).inversions = 0 := rfl
  rw [hi, pow_zero, one_smul]
  simp only [hf, op_id]
  change integerTensorMap (C.map (𝟙 (op ⦋0⦌))) (D.map (𝟙 (op ⦋0⦌))) ≫
    integerTensorMap (C.map (𝟙 (op ⦋0⦌))) (D.map (𝟙 (op ⦋0⦌))) = _
  simp only [C.map_id, D.map_id, integerTensorMap_id, Category.id_comp]
  rfl

/-- 概要：恒等と AW→shuffle の普遍な差は零次で零。
方針：実零次の合成の計算を普遍作用素の単射性で普遍模型へ戻す。
規約：KST A.5、増大を落とさずに零次を処理する。
使われ方：比較ホモトピーの再帰の初期条件。 -/
lemma ezUniversalDifference_zero : ezUniversalDifference.{u} 0 = 0 := by
  apply simplexPairOperation_injective 0 (op ⦋0⦌)
  rw [simplexPairOperation_ezDifference, ezComposite_zero, sub_self, map_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
