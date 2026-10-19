module
public import SerrePositivity.KST.ProExcision.IdealRowMatrixAction

/-!
# 行群への左乗法と右行列作用の実可換性

概要：両側イデアル内の行ベクトルへの左乗法を実群準同型として構成する。
方針：左吸収と結合律を使い、右行列作用と係数変更に対する自然性を示す。
規約：KST Proposition 4.14、SW92 §1.2 の行側。中心性はこの段階では不要。
使われ方：反対係数環の列の右乗法から移す実行側の写像。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：両側イデアル内の左乗法の実加法群準同型。
方針：左吸収と左分配法則を使う。
規約：SW92 §1.2。使われ方：行ベクトルへの左乗法。 -/
def idealLeftMultiplication (J : TwoSidedIdeal R) (a : R) : J →+ J where
  toFun x := ⟨a * (x : R), J.mul_mem_left _ _ x.property⟩
  map_zero' := by apply Subtype.ext; exact mul_zero a
  map_add' x y := by apply Subtype.ext; exact mul_add a (x : R) (y : R)

/-- 概要：行ベクトルへの左乗法の実群準同型。
方針：成分ごとの実加法群準同型を乗法表記へ移す。
規約：SW92 §1.2。使われ方：実行側相対写像のファイバー成分。 -/
def idealVectorLeftHom (J : TwoSidedIdeal R) (ι : Type v) (a : R) :
    Multiplicative (ι → J) →* Multiplicative (ι → J) :=
  (show (ι → J) →+ (ι → J) from
    { toFun := fun v i ↦ idealLeftMultiplication J a (v i)
      map_zero' := by funext i; exact map_zero (idealLeftMultiplication J a)
      map_add' := by intro v w; funext i; exact map_add (idealLeftMultiplication J a) (v i) (w i)
    }).toMultiplicative

/-- 概要：行ベクトルの左乗法は全ての右行列作用と可換。
方針：有限和への左分配と非可換な積の結合律を使う。
規約：KST Proposition 4.14 の行側、中心性不要。
使われ方：行側左乗法の実同変射。 -/
lemma idealVectorLeftHom_equivariant (n : ℕ) (J : TwoSidedIdeal R) (a : R)
    (M : (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ) (v : Multiplicative (Fin n → J)) :
    idealVectorLeftHom J (Fin n) a (idealRowMatrixAction n J M v) =
      idealRowMatrixAction n J M (idealVectorLeftHom J (Fin n) a v) := by
  change (fun j ↦ idealLeftMultiplication J a
      (idealRowMatrixVecHom n J (MulOpposite.unop M) v.toAdd j)) =
    idealRowMatrixVecHom n J (MulOpposite.unop M)
      (fun i ↦ idealLeftMultiplication J a (v.toAdd i))
  funext j
  apply Subtype.ext
  change a * (∑ i, (v.toAdd i : R) * MulOpposite.unop M i j) =
    ∑ i, (a * (v.toAdd i : R)) * MulOpposite.unop M i j
  simp only [Finset.mul_sum, mul_assoc]

/-- 概要：行群の左乗法は指定元を保つ係数射に自然。
方針：各成分で環準同型の乗法保存を使う。
規約：SW92 §1.2。使われ方：実行側写像の面・退化への自然性。 -/
lemma idealVectorLeftHom_functorial {R' : Type w} [Ring R']
    (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R') (ι : Type v)
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    (a : R) (a' : R') (ha : f a = a') (v : Multiplicative (ι → J)) :
    idealVectorMap J J' ι f hf (idealVectorLeftHom J ι a v) =
      idealVectorLeftHom J' ι a' (idealVectorMap J J' ι f hf v) := by
  change (fun i ↦ idealCoefficientAddHom J J' f hf
      (idealLeftMultiplication J a (v.toAdd i))) =
    (fun i ↦ idealLeftMultiplication J' a'
      (idealCoefficientAddHom J J' f hf (v.toAdd i)))
  funext i
  apply Subtype.ext
  change f (a * (v.toAdd i : R)) = a' * f (v.toAdd i : R)
  rw [map_mul, ha]

end SerrePositivity.KST.ProExcision
