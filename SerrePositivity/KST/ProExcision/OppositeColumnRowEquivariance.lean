module
public import SerrePositivity.KST.ProExcision.UnitizationIdealOpposite
public import SerrePositivity.KST.ProExcision.HatGLReverseOppositeMatrix
public import SerrePositivity.KST.ProExcision.IdealRowMatrixAction

/-!
# 反対転置による列作用と行作用の実比較

概要：反対係数環の列への左作用が、実反対転置により元の行への右作用になる。
方針：実核イデアル同型を有限和に通し、乗法の順序逆転を各成分で使う。
規約：KST Proposition 4.14、SW92 §1.2。係数の可換性は使わない。
使われ方：行側と列側の実半直積の乗法同型。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable (J : Type u) [NonUnitalRing J]

/-- 概要：反対核イデアル内の列群と元の行群の実乗法同型。
方針：実加法同型を加法群の乗法表記に移す。
規約：SW92 §1.2。使われ方：半直積比較の実群成分。 -/
def integerUnitizationIdealOpVectorMulEquiv (n : ℕ) :
    Multiplicative (Fin n → integerUnitizationIdeal Jᵐᵒᵖ) ≃*
      Multiplicative (Fin n → integerUnitizationIdeal J) :=
  (integerUnitizationIdealOpVectorAddEquiv J (Fin n)).toMultiplicative

/-- 概要：反対転置は反対係数の列の左作用を元の行の右作用へ移す。
方針：核イデアル同型を周囲環に移し、有限和と積の反転を評価する。
規約：KST Proposition 4.14、SW92 §1.2。全行列を許す。
使われ方：実半直積比較の乗法保存。 -/
lemma integerUnitizationIdealOpVector_equivariant (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ Jᵐᵒᵖ))
    (v : Multiplicative (Fin n → integerUnitizationIdeal Jᵐᵒᵖ)) :
    integerUnitizationIdealOpVectorMulEquiv J n
        (idealMatrixAction n (integerUnitizationIdeal Jᵐᵒᵖ) A v) =
      idealRowMatrixAction n (integerUnitizationIdeal J)
        (integerUnitizationMatrixOpEquiv J n A)
        (integerUnitizationIdealOpVectorMulEquiv J n v) := by
  change integerUnitizationIdealOpVectorAddEquiv J (Fin n)
      (idealMatrixVecHom n (integerUnitizationIdeal Jᵐᵒᵖ) A v.toAdd) =
    idealRowMatrixVecHom n (integerUnitizationIdeal J)
      (MulOpposite.unop (integerUnitizationMatrixOpEquiv J n A))
      (integerUnitizationIdealOpVectorAddEquiv J (Fin n) v.toAdd)
  funext j
  apply Subtype.ext
  change (integerUnitizationIdealOpAddEquiv J _ : Unitization ℤ J) =
    ∑ i, (integerUnitizationIdealOpAddEquiv J (v.toAdd i) : Unitization ℤ J) *
      MulOpposite.unop (integerUnitizationOpEquiv J (A j i))
  rw [integerUnitizationIdealOpAddEquiv_coe]
  change MulOpposite.unop (integerUnitizationOpEquiv J
    (∑ i, A j i * (v.toAdd i : Unitization ℤ Jᵐᵒᵖ))) = _
  simp only [map_sum, map_mul, Finset.unop_sum, MulOpposite.unop_mul,
    integerUnitizationIdealOpAddEquiv_coe]

/-- 概要：反対核イデアルの行・列群の実比較は係数準同型に自然。
方針：ベクトルの各成分に核イデアルの実自然性を適用する。
規約：SW92 §1.2。使われ方：実半直積同型の面・退化との可換性。 -/
lemma integerUnitizationIdealOpVectorMulEquiv_natural
    {K : Type u} [NonUnitalRing K] (f : J →ₙ+* K) (n : ℕ)
    (v : Multiplicative (Fin n → integerUnitizationIdeal Jᵐᵒᵖ)) :
    integerUnitizationIdealOpVectorMulEquiv K n
        (idealVectorMap (integerUnitizationIdeal Jᵐᵒᵖ) (integerUnitizationIdeal Kᵐᵒᵖ)
          (Fin n) (integerUnitizationMap (NonUnitalRingHom.op f))
          (integerUnitizationMap_ideal (NonUnitalRingHom.op f)) v) =
      idealVectorMap (integerUnitizationIdeal J) (integerUnitizationIdeal K) (Fin n)
        (integerUnitizationMap f) (integerUnitizationMap_ideal f)
        (integerUnitizationIdealOpVectorMulEquiv J n v) := by
  change (fun i ↦ integerUnitizationIdealOpAddEquiv K
      (idealCoefficientAddHom _ _ (integerUnitizationMap (NonUnitalRingHom.op f))
        (integerUnitizationMap_ideal (NonUnitalRingHom.op f)) (v.toAdd i))) =
    (fun i ↦ idealCoefficientAddHom _ _ (integerUnitizationMap f)
      (integerUnitizationMap_ideal f) (integerUnitizationIdealOpAddEquiv J (v.toAdd i)))
  funext i
  exact integerUnitizationIdealOpAddEquiv_natural J f (v.toAdd i)

end SerrePositivity.KST.ProExcision
