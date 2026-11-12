module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleVerticalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleInsertSign

/-!
# 純粋境界添字の実テンソル写像への適用

概要：面番号による挿入が作る境界の実写像と符号を、各因子の通常境界へ同定する。
方針：二つの単体写像の面の等式を反変な係数へ送り、テンソル写像の合成則を使う。
規約：KST Construction A.5 の標準 shuffle。水平・垂直の両方の端点と内部を含む。
使われ方：純粋境界和の有限な添字の同値に適用する各項の等式。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：水平面番号による挿入の実テンソル境界写像は第一因子の面の前合成。
方針：二つの単体写像の面の一致を反変関手で写し、合成のテンソルにする。
規約：KST A.5、第一因子の全ての面。
使われ方：水平境界和の各項と通常境界和の各項の同定。 -/
lemma horizontalShuffleFace_map {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (p + 2)) :
    integerTensorMap (C.map (s.insertHorizontal (s.horizontalFacePosition i)).left.op)
        (D.map ((s.insertHorizontal (s.horizontalFacePosition i)).right
          (show (p + 1) + q = n + 1 by omega)).op) ≫
      integerTensorMap (C.δ (s.horizontalFaceVertex i)) (D.δ (s.horizontalFaceVertex i)) =
    integerTensorMap (C.δ i) (𝟙 (D.obj (op ⦋q⦌))) ≫
      integerTensorMap (C.map s.left.op) (D.map (s.right h).op) := by
  have hc := congrArg (fun f ↦ C.map f.op) (s.horizontalFace_left i)
  have hd := congrArg (fun f ↦ D.map f.op) (s.horizontalFace_right h i)
  simp only [op_comp, C.map_comp] at hc
  simp only [op_comp, D.map_comp] at hd
  rw [← integerTensorMap_comp, ← integerTensorMap_comp, Category.id_comp]
  exact congrArg₂ integerTensorMap hc hd

/-- 概要：垂直面番号による挿入の実テンソル境界写像は第二因子の面の前合成。
方針：二つの単体写像の面の一致を反変関手で写し、合成のテンソルにする。
規約：KST A.5、第二因子の全ての面。
使われ方：垂直境界和の各項と通常境界和の各項の同定。 -/
lemma verticalShuffleFace_map {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (q + 2)) :
    integerTensorMap (C.map (s.insertVertical (s.verticalFacePosition h i)).left.op)
        (D.map ((s.insertVertical (s.verticalFacePosition h i)).right
          (show p + (q + 1) = n + 1 by omega)).op) ≫
      integerTensorMap (C.δ (s.verticalFaceVertex h i)) (D.δ (s.verticalFaceVertex h i)) =
    integerTensorMap (𝟙 (C.obj (op ⦋p⦌))) (D.δ i) ≫
      integerTensorMap (C.map s.left.op) (D.map (s.right h).op) := by
  have hc := congrArg (fun f ↦ C.map f.op) (s.verticalFace_left h i)
  have hd := congrArg (fun f ↦ D.map f.op) (s.verticalFace_right h i)
  simp only [op_comp, C.map_comp] at hc
  simp only [op_comp, D.map_comp] at hd
  rw [← integerTensorMap_comp, ← integerTensorMap_comp, Category.id_comp]
  exact congrArg₂ integerTensorMap hc hd

/-- 概要：水平面番号からの境界項の符号は面番号の通常符号に一致。
方針：端点の逆転数の公式と内部の挿入符号の公式を使う。
規約：KST A.5、全ての第一因子の面。
使われ方：添字の同値に沿う水平境界項の符号の比較。 -/
lemma ShuffleIndex.horizontalFace_sign {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (p + 2)) :
    (-1 : ℤ) ^ (s.horizontalFaceVertex i : ℕ) *
      (-1 : ℤ) ^ (s.insertHorizontal (s.horizontalFacePosition i)).inversions =
        (-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ s.inversions := by
  by_cases h₀ : i = 0
  · subst i
    have hi := s.insertHorizontal_inversions h 0
    rw [s.right_zero, add_zero] at hi
    simp only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl,
      ite_true, dite_true, Fin.val_zero, hi]
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      have ht := s.insertHorizontal_face_sign h (Fin.last n)
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true, Fin.val_last, s.left_last] using ht
    · let a := s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)
      have ht := s.insertHorizontal_face_sign h a.castSucc
      have he := congrArg Fin.val (s.horizontalFaceInterior_coface i h₀ h₁)
      change (s.left.toOrderHom a.castSucc : ℕ) + 1 = (i : ℕ) at he
      rw [he] at ht
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_right h₁, dite_eq_right h₁, Fin.val_succ] using ht

/-- 概要：垂直面番号からの境界項の符号は全複体の通常の垂直符号に一致。
方針：端点の逆転数の公式と内部の垂直挿入符号の公式を使う。
規約：KST A.5、外側の垂直符号は (−1)^p。
使われ方：添字の同値に沿う垂直境界項の符号の比較。 -/
lemma ShuffleIndex.verticalFace_sign {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (i : Fin (q + 2)) :
    (-1 : ℤ) ^ (s.verticalFaceVertex h i : ℕ) *
      (-1 : ℤ) ^ (s.insertVertical (s.verticalFacePosition h i)).inversions =
        (-1 : ℤ) ^ p * ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ s.inversions) := by
  by_cases h₀ : i = 0
  · subst i
    have hi := s.insertVertical_inversions h 0
    rw [s.left_zero, Nat.sub_zero] at hi
    simp only [verticalFaceVertex, verticalFacePosition, horizontalFaceVertex, horizontalFacePosition,
      ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true, Fin.val_zero, hi, pow_zero, one_mul]
    rw [pow_add, mul_comm]
  · by_cases h₁ : i = Fin.last (q + 1)
    · subst i
      have ht := s.insertVertical_face_sign h (Fin.last n)
      simpa only [verticalFaceVertex, verticalFacePosition, horizontalFaceVertex, horizontalFacePosition,
        ite_eq_right h₀, dite_eq_right h₀, ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true,
        Fin.val_last, s.right_last] using ht
    · let a := (s.transpose h).horizontalStep (horizontalFaceInteriorRank i h₀ h₁)
      have ht := s.insertVertical_face_sign h a.castSucc
      have he := congrArg Fin.val ((s.transpose h).horizontalFaceInterior_coface i h₀ h₁)
      rw [s.transpose_left] at he
      change ((s.right h).toOrderHom a.castSucc : ℕ) + 1 = (i : ℕ) at he
      rw [he] at ht
      simpa only [verticalFaceVertex, verticalFacePosition, horizontalFaceVertex, horizontalFacePosition,
        ite_eq_right h₀, dite_eq_right h₀, ite_eq_right h₁, dite_eq_right h₁, Fin.val_succ] using ht

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
