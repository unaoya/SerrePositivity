module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleBoundaryMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Shuffle

/-!
# shuffle の純粋水平・垂直境界和

概要：純粋境界の実写像の有限和を、各因子の通常の交代境界の前合成へ同定する。
方針：境界添字の実同値と各項の写像・符号の一致を使い、有限和を分配する。
規約：KST Construction A.5 の標準 shuffle、非被約な零次を含む。
使われ方：全混合境界和の消滅と合わせる shuffle の鎖写像性。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：面と shuffle の二つの符号を含む純粋水平境界の実写像。
方針：大きい shuffle の退化写像の後に指定面を合成する。
規約：KST A.5、元の二重次数は p+1,q。
使われ方：水平境界和の各項。 -/
def horizontalShuffleWeight {p q n : ℕ} (h : p + q = n) (z : HorizontalShuffleBoundaryIndex p n) :=
  (-1 : ℤ) ^ (z.val.2 : ℕ) •
    ((-1 : ℤ) ^ z.val.1.inversions •
      (integerTensorMap (C.map z.val.1.left.op)
          (D.map (z.val.1.right (show (p + 1) + q = n + 1 by omega)).op) ≫
        integerTensorMap (C.δ z.val.2) (D.δ z.val.2)))

/-- 概要：面と shuffle の二つの符号を含む純粋垂直境界の実写像。
方針：大きい shuffle の退化写像の後に指定面を合成する。
規約：KST A.5、元の二重次数は p,q+1。
使われ方：垂直境界和の各項。 -/
def verticalShuffleWeight {p q n : ℕ} (h : p + q = n) (z : VerticalShuffleBoundaryIndex p q n h) :=
  (-1 : ℤ) ^ (z.val.2 : ℕ) •
    ((-1 : ℤ) ^ z.val.1.inversions •
      (integerTensorMap (C.map z.val.1.left.op)
          (D.map (z.val.1.right (show p + (q + 1) = n + 1 by omega)).op) ≫
        integerTensorMap (C.δ z.val.2) (D.δ z.val.2)))

/-- 概要：水平境界の実同値は各項を第一因子の境界と小さい shuffle の合成へ送る。
方針：実テンソル写像と符号の一致を合成する。
規約：KST A.5。使われ方：純粋水平境界和の並べ替え。 -/
lemma horizontalShuffleWeight_equiv {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (p + 2)) :
    horizontalShuffleWeight C D h (horizontalShuffleBoundaryEquiv p n (s, i)) =
      (-1 : ℤ) ^ (i : ℕ) • ((-1 : ℤ) ^ s.inversions •
        (integerTensorMap (C.δ i) (𝟙 (D.obj (op ⦋q⦌))) ≫
          integerTensorMap (C.map s.left.op) (D.map (s.right h).op))) := by
  change (-1 : ℤ) ^ (s.horizontalFaceVertex i : ℕ) •
    ((-1 : ℤ) ^ (s.insertHorizontal (s.horizontalFacePosition i)).inversions • _) = _
  change (-1 : ℤ) ^ (s.horizontalFaceVertex i : ℕ) •
    ((-1 : ℤ) ^ (s.insertHorizontal (s.horizontalFacePosition i)).inversions •
      (integerTensorMap (C.map (s.insertHorizontal (s.horizontalFacePosition i)).left.op)
        (D.map ((s.insertHorizontal (s.horizontalFacePosition i)).right
          (show (p + 1) + q = n + 1 by omega)).op) ≫
        integerTensorMap (C.δ (s.horizontalFaceVertex i))
          (D.δ (s.horizontalFaceVertex i)))) = _
  rw [horizontalShuffleFace_map C D s h i]
  simp only [smul_smul]
  rw [s.horizontalFace_sign h i]

/-- 概要：垂直境界の実同値は各項を第二因子の境界と小さい shuffle の合成へ送る。
方針：実テンソル写像と全複体の垂直符号の一致を合成する。
規約：KST A.5。使われ方：純粋垂直境界和の並べ替え。 -/
lemma verticalShuffleWeight_equiv {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (q + 2)) :
    verticalShuffleWeight C D h (verticalShuffleBoundaryEquiv p q n h (s, i)) =
      (-1 : ℤ) ^ p • ((-1 : ℤ) ^ (i : ℕ) • ((-1 : ℤ) ^ s.inversions •
        (integerTensorMap (𝟙 (C.obj (op ⦋p⦌))) (D.δ i) ≫
          integerTensorMap (C.map s.left.op) (D.map (s.right h).op)))) := by
  simp only [verticalShuffleWeight, verticalShuffleBoundaryEquiv_apply]
  rw [verticalShuffleFace_map C D s h i]
  simp only [smul_smul]
  rw [s.verticalFace_sign h i]

/-- 概要：純粋水平境界和は第一因子の通常の交代境界を前合成した shuffle の和。
方針：水平境界添字の同値で移し、shuffle の有限和と合成を分配する。
規約：KST Construction A.5、任意の単体的整数加群に成立。
使われ方：shuffle の鎖写像性の第一因子の微分。 -/
theorem horizontalShuffle_sum {p q n : ℕ} (h : p + q = n) :
    (∑ z : HorizontalShuffleBoundaryIndex p n, horizontalShuffleWeight C D h z) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (integerTensorMap (C.δ i) (𝟙 (D.obj (op ⦋q⦌))) ≫ shuffleBidegree C D p q n h) := by
  rw [horizontalShuffleBoundary_sum]
  simp_rw [horizontalShuffleWeight_equiv]
  rw [Finset.sum_comm]
  simp only [shuffleBidegree, Preadditive.comp_sum, Preadditive.comp_zsmul, Finset.smul_sum]

/-- 概要：純粋垂直境界和は第二因子の通常の交代境界を前合成した shuffle の和。
方針：垂直境界添字の同値で移し、shuffle の有限和と合成を分配する。
規約：KST A.5、外側の垂直符号 (−1)^p を含む。
使われ方：shuffle の鎖写像性の第二因子の微分。 -/
theorem verticalShuffle_sum {p q n : ℕ} (h : p + q = n) :
    (∑ z : VerticalShuffleBoundaryIndex p q n h, verticalShuffleWeight C D h z) =
      (-1 : ℤ) ^ p •
        (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
          (integerTensorMap (𝟙 (C.obj (op ⦋p⦌))) (D.δ i) ≫ shuffleBidegree C D p q n h)) := by
  rw [verticalShuffleBoundary_sum]
  simp_rw [verticalShuffleWeight_equiv]
  rw [Finset.sum_comm]
  simp only [shuffleBidegree, Preadditive.comp_sum, Preadditive.comp_zsmul, Finset.smul_sum]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
