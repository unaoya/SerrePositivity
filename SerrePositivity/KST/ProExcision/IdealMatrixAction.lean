module
public import SerrePositivity.KST.ProExcision.MatrixBlockAction
public import SerrePositivity.KST.ProExcision.IdealRightColumn
public import SerrePositivity.KST.ProExcision.Prop414

/-!
# イデアル内の列ベクトルへの左行列作用

概要：任意の行列の左積はイデアル内の列ベクトルの加法群に作用し、右乗法と可換。
方針：イデアルの左吸収と行列積の結合律を使う。
規約：KST Lemma 4.16 の Q と φ、可換性・中心性は不要。
使われ方：μ 版 A.5 の始域と第二因子の実外部作用。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：イデアル内の列ベクトルへの行列の左積の加法群準同型。
方針：各成分をイデアル内の有限和とし、分配法則で加法保存を示す。
規約：KST 4.16、全行列を許す。
使われ方：Q の外部行列作用の構成。 -/
def idealMatrixVecHom (n : ℕ) (J : TwoSidedIdeal R) (M : Matrix (Fin n) (Fin n) R) :
    (Fin n → J) →+ (Fin n → J) where
  toFun v i := ⟨∑ j, M i j * (v j : R), J.finsetSum_mem _ _ (fun j _ ↦ J.mul_mem_left _ _ (v j).property)⟩
  map_zero' := by
    funext i
    apply Subtype.ext
    change (∑ j, M i j * 0) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  map_add' v w := by
    funext i
    apply Subtype.ext
    change (∑ j, M i j * ((v j : R) + (w j : R))) = (∑ j, M i j * (v j : R)) + ∑ j, M i j * (w j : R)
    simp only [mul_add, Finset.sum_add_distrib]

/-- 概要：イデアル内の列ベクトルの群の外部行列モノイド作用。
方針：単位行列の積と二つの行列の合成の列ベクトル公式を使う。
規約：KST Lemma 4.16 の始域と Q の外部 G。
使われ方：A.5 の入力と群準同型の同変性。 -/
def idealMatrixAction (n : ℕ) (J : TwoSidedIdeal R) :
    Matrix (Fin n) (Fin n) R →* Monoid.End (Multiplicative (Fin n → J)) where
  toFun M := (idealMatrixVecHom n J M).toMultiplicative
  map_one' := by
    apply MonoidHom.ext
    intro v
    change idealMatrixVecHom n J 1 v.toAdd = v.toAdd
    funext i
    apply Subtype.ext
    change (∑ j, (1 : Matrix (Fin n) (Fin n) R) i j * (v.toAdd j : R)) = (v.toAdd i : R)
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply MonoidHom.ext
    intro v
    change idealMatrixVecHom n J (M * N) v.toAdd = idealMatrixVecHom n J M (idealMatrixVecHom n J N v.toAdd)
    funext i
    apply Subtype.ext
    change ((M * N) *ᵥ (fun j ↦ (v.toAdd j : R))) i =
      (M *ᵥ (N *ᵥ (fun j ↦ (v.toAdd j : R)))) i
    exact congrFun (Matrix.mulVec_mulVec (fun j ↦ (v.toAdd j : R)) M N).symm i

/-- 概要：イデアル内の右乗法は全行列の左作用と可換。
方針：各成分で有限和の右分配と結合律を使う。
規約：KST Lemma 4.16 の非可換版 φ、中心性を使わない。
使われ方：因子内の α と大きい φ の行列同変性。 -/
lemma idealVectorRightHom_equivariant (n : ℕ) (J : TwoSidedIdeal R) (a : R)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    idealVectorRightHom J (Fin n) a (idealMatrixAction n J M v) =
      idealMatrixAction n J M (idealVectorRightHom J (Fin n) a v) := by
  change idealRightMultiplication J a ∘ idealMatrixVecHom n J M v.toAdd =
    idealMatrixVecHom n J M (fun i ↦ idealRightMultiplication J a (v.toAdd i))
  funext i
  apply Subtype.ext
  change (∑ j, M i j * (v.toAdd j : R)) * a = ∑ j, M i j * ((v.toAdd j : R) * a)
  simp only [Finset.sum_mul, mul_assoc]

end SerrePositivity.KST.ProExcision
