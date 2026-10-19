module
public import SerrePositivity.KST.ProExcision.MatrixActionCoefficientMap
public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# 両側イデアル内の行ベクトルへの実右行列作用

概要：行ベクトルの右行列積を反対行列モノイドの左作用として構成する。
方針：右吸収と有限和、非可換な行列積の結合律を用いる。
規約：KST Proposition 4.14、SW92 §1.2 の行側。イデアルの可換性は不要。
使われ方：実行側半直積と列側の反対転置の同定。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：両側イデアル内の行ベクトルへの実右行列積。
方針：各成分を右吸収でイデアルに入り続ける有限和として定義する。
規約：SW92 §1.2、非可換係数。使われ方：実右行列作用の各元。 -/
def idealRowMatrixVecHom (n : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) : (Fin n → J) →+ (Fin n → J) where
  toFun v j := ⟨∑ i, (v i : R) * M i j,
    J.finsetSum_mem _ _ (fun i _ ↦ J.mul_mem_right _ _ (v i).property)⟩
  map_zero' := by
    funext j
    apply Subtype.ext
    change (∑ i, (0 : R) * M i j) = 0
    simp only [zero_mul, Finset.sum_const_zero]
  map_add' v w := by
    funext j
    apply Subtype.ext
    change (∑ i, ((v i : R) + (w i : R)) * M i j) =
      (∑ i, (v i : R) * M i j) + ∑ i, (w i : R) * M i j
    simp only [add_mul, Finset.sum_add_distrib]

/-- 概要：反対行列モノイドのイデアル内の行群への実作用。
方針：右行列積の単位律と結合律を準同型の法則として使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：行側半直積の実乗法。 -/
def idealRowMatrixAction (n : ℕ) (J : TwoSidedIdeal R) :
    (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ →* Monoid.End (Multiplicative (Fin n → J)) where
  toFun M := (idealRowMatrixVecHom n J (MulOpposite.unop M)).toMultiplicative
  map_one' := by
    apply MonoidHom.ext
    intro v
    change idealRowMatrixVecHom n J 1 v.toAdd = v.toAdd
    funext j
    apply Subtype.ext
    change (∑ i, (v.toAdd i : R) * (1 : Matrix (Fin n) (Fin n) R) i j) = (v.toAdd j : R)
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply MonoidHom.ext
    intro v
    change idealRowMatrixVecHom n J (MulOpposite.unop N * MulOpposite.unop M) v.toAdd =
      idealRowMatrixVecHom n J (MulOpposite.unop M)
        (idealRowMatrixVecHom n J (MulOpposite.unop N) v.toAdd)
    funext j
    apply Subtype.ext
    exact congrFun (Matrix.vecMul_vecMul (fun i ↦ (v.toAdd i : R))
      (MulOpposite.unop N) (MulOpposite.unop M)).symm j

/-- 概要：行群の実右行列作用は係数準同型に自然。
方針：各成分で有限和と積の保存を使う。
規約：SW92 §1.2、両側イデアルを保つ係数写像。
使われ方：行側の面・退化と乗法の整合。 -/
lemma idealRowMatrixAction_functorial {R' : Type v} [Ring R']
    (n : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    (M : (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ) (v : Multiplicative (Fin n → J)) :
    idealVectorMap J J' (Fin n) f hf (idealRowMatrixAction n J M v) =
      idealRowMatrixAction n J' (MulOpposite.op ((MulOpposite.unop M).map f))
        (idealVectorMap J J' (Fin n) f hf v) := by
  change (fun j ↦ idealCoefficientAddHom J J' f hf
      (idealRowMatrixVecHom n J (MulOpposite.unop M) v.toAdd j)) =
    idealRowMatrixVecHom n J' ((MulOpposite.unop M).map f)
      (fun i ↦ idealCoefficientAddHom J J' f hf (v.toAdd i))
  funext j
  apply Subtype.ext
  change f (∑ i, (v.toAdd i : R) * MulOpposite.unop M i j) =
    ∑ i, f (v.toAdd i : R) * f (MulOpposite.unop M i j)
  simp only [map_sum, map_mul]

end SerrePositivity.KST.ProExcision
