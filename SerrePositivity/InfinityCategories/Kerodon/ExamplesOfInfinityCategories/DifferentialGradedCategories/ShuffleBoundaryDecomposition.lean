module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleBoundaryPartition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePureSum

/-!
# shuffle の全境界和の実写像への分解

概要：境界の三分を実テンソル写像へ適用し、混合項を除去する。
方針：混合和の対合による消滅と、純粋境界和の二因子の境界への同定を使う。
規約：KST Construction A.5、非被約な零次を含む。
使われ方：標準 shuffle の鎖写像性の組立。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：全境界の一項に二つの交代符号を付けた実写像。
方針：shuffle の退化写像の後に対角の面を適用する。
規約：KST A.5、全次数は n+1。
使われ方：境界の分類と交代面微分との接続。 -/
def shuffleBoundaryWeight {p q n : ℕ} (h : p + q = n + 1)
    (z : ShuffleIndex p (n + 1) × Fin (n + 2)) :=
  (-1 : ℤ) ^ (z.2 : ℕ) • ((-1 : ℤ) ^ z.1.inversions •
    (integerTensorMap (C.map z.1.left.op) (D.map (z.1.right h).op) ≫
      integerTensorMap (C.δ z.2) (D.δ z.2)))

/-- 概要：実境界写像の混合項の和は零。
方針：内部頂点のない次数を分け、正の次数で固定点のない交換対合の定理を使う。
規約：KST A.5、係数に二倍の単射性を要求しない。
使われ方：全境界の純粋な二つの和への縮約。 -/
lemma shuffleBoundary_mixed_sum_zero {p q n : ℕ} (h : p + q = n + 1) :
    (∑ z : AllMixedShuffleBoundaryIndex p n,
      shuffleBoundaryWeight C D h (z.val.1, z.val.2.castSucc.succ)) = 0 := by
  cases n with
  | zero =>
    apply Finset.sum_eq_zero
    intro z _
    exact Fin.elim0 z.val.2
  | succ n =>
    simpa only [shuffleBoundaryWeight, shuffleMixedWeight, Fin.succ_castSucc,
      Fin.val_castSucc, Fin.val_succ] using
      shuffleMixed_sum_zero C D h

/-- 概要：shuffle の後の対角微分は全境界の実写像の二重和。
方針：交代面微分を展開し、二つの符号付き和に合成を分配する。
規約：KST A.5、正規化前の複体。
使われ方：境界添字の分類を鎖写像性に適用する。 -/
lemma shuffleBidegree_boundary {p q n : ℕ} (h : p + q = n + 1) :
    shuffleBidegree C D p q (n + 1) h ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n =
    ∑ s : ShuffleIndex p (n + 1), ∑ k : Fin (n + 2),
      shuffleBoundaryWeight C D h (s, k) := by
  rw [shuffleBidegree, alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- 概要：全境界の微分は純粋水平和と純粋垂直和の和。
方針：全境界の有限分類を適用し、混合和を零にする。
規約：KST Construction A.5、全ての二重次数に成立。
使われ方：全テンソルの水平・垂直微分との比較。 -/
theorem shuffleBidegree_boundary_pure {p q n : ℕ} (h : p + q = n + 1) :
    shuffleBidegree C D p q (n + 1) h ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n =
    (∑ z : AllHorizontalShuffleBoundaryIndex p n, shuffleBoundaryWeight C D h z.val) +
      ∑ z : AllVerticalShuffleBoundaryIndex p n, shuffleBoundaryWeight C D h z.val := by
  rw [shuffleBidegree_boundary, shuffleBoundaryPartition_sum,
    shuffleBoundary_mixed_sum_zero, add_zero]

/-- 概要：垂直境界条件は補集合の水平境界条件と一致。
方針：補集合への所属を元の集合への非所属と読む。
規約：KST A.5。使われ方：全次数の垂直和を既存の純粋境界和へ送る。 -/
lemma verticalShuffleFace_iff_transpose {p q n : ℕ} (h : p + q = n + 1)
    (s : ShuffleIndex p (n + 1)) (k : Fin (n + 2)) :
    IsVerticalShuffleFace s k ↔ IsHorizontalShuffleFace (s.transpose h) k := by
  change IsUniformShuffleFace (fun a ↦ a ∉ s.val) k ↔
    IsUniformShuffleFace (fun a ↦ a ∈ s.valᶜ) k
  simp only [Finset.mem_compl]

/-- 概要：垂直属性と補集合による垂直属性の部分型は同値。
方針：対の値を変えず、同値な境界条件の証明だけを移す。
規約：KST A.5。使われ方：純粋垂直和の公式への添字変換。 -/
def allVerticalShuffleBoundaryEquiv (p q n : ℕ) (h : p + q = n) :
    AllVerticalShuffleBoundaryIndex p n ≃ VerticalShuffleBoundaryIndex p q n h where
  toFun z := ⟨z.val, (verticalShuffleFace_iff_transpose (by omega) z.val.1 z.val.2).mp z.property⟩
  invFun z := ⟨z.val, (verticalShuffleFace_iff_transpose (by omega) z.val.1 z.val.2).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 概要：水平ステップが零なら純粋水平境界は存在しない。
方針：水平集合の要素数が零であることを使う。
規約：KST A.5。使われ方：全テンソルの零次水平微分。 -/
lemma shuffleFace_not_horizontal_zero {n : ℕ} (s : ShuffleIndex 0 (n + 1))
    (k : Fin (n + 2)) : ¬ IsHorizontalShuffleFace s k := by
  have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property
  rintro (⟨_, hm⟩ | ⟨_, hm⟩ | ⟨a, _, hm, _⟩) <;> simp only [hs, Finset.notMem_empty] at hm

/-- 概要：垂直ステップが零なら純粋垂直境界は存在しない。
方針：補集合を水平集合として零水平次数の結果を適用する。
規約：KST A.5。使われ方：全テンソルの零次垂直微分。 -/
lemma shuffleFace_not_vertical_zero {p n : ℕ} (h : p + 0 = n + 1)
    (s : ShuffleIndex p (n + 1)) (k : Fin (n + 2)) : ¬ IsVerticalShuffleFace s k := by
  rw [verticalShuffleFace_iff_transpose h]
  exact shuffleFace_not_horizontal_zero (s.transpose h) k

/-- 概要：零水平次数では純粋水平境界和は零。
方針：各添字の水平条件の不可能性を使う。
規約：KST A.5。使われ方：shuffle の水平微分の端。 -/
lemma shuffleBoundary_horizontal_zero {q n : ℕ} (h : 0 + q = n + 1) :
    (∑ z : AllHorizontalShuffleBoundaryIndex 0 n, shuffleBoundaryWeight C D h z.val) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  exact False.elim (shuffleFace_not_horizontal_zero z.val.1 z.val.2 z.property)

/-- 概要：零垂直次数では純粋垂直境界和は零。
方針：各添字の垂直条件の不可能性を使う。
規約：KST A.5。使われ方：shuffle の垂直微分の端。 -/
lemma shuffleBoundary_vertical_zero {p n : ℕ} (h : p + 0 = n + 1) :
    (∑ z : AllVerticalShuffleBoundaryIndex p n, shuffleBoundaryWeight C D h z.val) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  exact False.elim (shuffleFace_not_vertical_zero h z.val.1 z.val.2 z.property)

/-- 概要：正の水平次数では純粋水平境界和は第一因子の境界の前合成。
方針：全次数の境界型を既存の水平境界型として読む。
規約：KST A.5。使われ方：全テンソルの水平微分との比較。 -/
lemma shuffleBoundary_horizontal_succ {p q n : ℕ} (h : p + q = n) :
    (∑ z : AllHorizontalShuffleBoundaryIndex (p + 1) n,
      shuffleBoundaryWeight C D (show (p + 1) + q = n + 1 by omega) z.val) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (integerTensorMap (C.δ i) (𝟙 (D.obj (op ⦋q⦌))) ≫ shuffleBidegree C D p q n h) :=
  horizontalShuffle_sum C D h

/-- 概要：正の垂直次数では純粋垂直境界和は第二因子の境界の前合成。
方針：垂直属性の同値で添字を移し、既存の垂直境界和へ同定する。
規約：KST A.5、全複体の符号 (−1)^p を含む。
使われ方：全テンソルの垂直微分との比較。 -/
lemma shuffleBoundary_vertical_succ {p q n : ℕ} (h : p + q = n) :
    (∑ z : AllVerticalShuffleBoundaryIndex p n,
      shuffleBoundaryWeight C D (show p + (q + 1) = n + 1 by omega) z.val) =
      (-1 : ℤ) ^ p •
        (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
          (integerTensorMap (𝟙 (C.obj (op ⦋p⦌))) (D.δ i) ≫ shuffleBidegree C D p q n h)) := by
  have ht := Fintype.sum_equiv (allVerticalShuffleBoundaryEquiv p q n h)
    (fun z ↦ shuffleBoundaryWeight C D (show p + (q + 1) = n + 1 by omega) z.val)
    (verticalShuffleWeight C D h) (fun _ ↦ rfl)
  rw [ht]
  exact verticalShuffle_sum C D h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
