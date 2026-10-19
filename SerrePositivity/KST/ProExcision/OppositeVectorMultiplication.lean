module
public import SerrePositivity.KST.ProExcision.OppositeColumnRowEquivariance
public import SerrePositivity.KST.ProExcision.IdealLeftMultiplication
public import SerrePositivity.KST.ProExcision.NonUnitalVertexReverse

/-!
# 反対核イデアルの右乗法と元の核イデアルの左乗法

概要：実反対比較が列の右乗法を行の左乗法に移すことを証明する。
方針：単位化の実反対環同型の乗法保存と指定元の高次像の反転不変性を使う。
規約：KST Proposition 4.14、SW92 §1.2。係数の中心性はまだ使わない。
使われ方：実行側相対写像への列側零化の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：反対核イデアルの右乗法は実比較で元の左乗法に移る。
方針：各成分を周囲環に移し、反対環の積の順序逆転を使う。
規約：SW92 §1.2、非可換係数。使われ方：実半直積写像の比較。 -/
lemma integerUnitizationIdealOpVector_right_left (J : Type u) [NonUnitalRing J]
    (n : ℕ) (a : Unitization ℤ Jᵐᵒᵖ)
    (v : Multiplicative (Fin n → integerUnitizationIdeal Jᵐᵒᵖ)) :
    integerUnitizationIdealOpVectorMulEquiv J n
        (idealVectorRightHom (integerUnitizationIdeal Jᵐᵒᵖ) (Fin n) a v) =
      idealVectorLeftHom (integerUnitizationIdeal J) (Fin n)
        (MulOpposite.unop (integerUnitizationOpEquiv J a))
        (integerUnitizationIdealOpVectorMulEquiv J n v) := by
  change (fun i ↦ integerUnitizationIdealOpAddEquiv J
      (idealRightMultiplication (integerUnitizationIdeal Jᵐᵒᵖ) a (v.toAdd i))) =
    (fun i ↦ idealLeftMultiplication (integerUnitizationIdeal J)
      (MulOpposite.unop (integerUnitizationOpEquiv J a))
      (integerUnitizationIdealOpAddEquiv J (v.toAdd i)))
  funext i
  apply Subtype.ext
  change (integerUnitizationIdealOpAddEquiv J _ : Unitization ℤ J) =
    MulOpposite.unop (integerUnitizationOpEquiv J a) *
      (integerUnitizationIdealOpAddEquiv J (v.toAdd i) : Unitization ℤ J)
  rw [integerUnitizationIdealOpAddEquiv_coe, integerUnitizationIdealOpAddEquiv_coe]
  change MulOpposite.unop (integerUnitizationOpEquiv J
    ((v.toAdd i : Unitization ℤ Jᵐᵒᵖ) * a)) = _
  rw [map_mul, MulOpposite.unop_mul]

/-- 概要：反転した反対標準単位化の指定元は元の指定元に実比較で移る。
方針：非単位環の高次像の反転不変性と包含の保存を合成する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：実列右乗法と実行左乗法の係数を同定する。 -/
lemma NonUnitalSimplicialRing.reverseOppositeStandardVertex
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (k : SimplexCategoryᵒᵖ) :
    MulOpposite.unop (integerUnitizationOpEquiv (I.obj k)
      (I.reverseOpposite.standardIdeal.vertexElement
        (I.reverseOpposite.standardElement (MulOpposite.op a)) k).val) =
      (I.standardIdeal.vertexElement (I.standardElement a) k).val := by
  rw [I.reverseOpposite.standardVertexElement_coe, I.reverseOpposite_vertexValue,
    integerUnitizationOpEquiv_inr, MulOpposite.unop_op, I.standardVertexElement_coe]
  rfl

end SerrePositivity.KST.ProExcision
