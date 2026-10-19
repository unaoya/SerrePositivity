module
public import SerrePositivity.KST.ProExcision.SimplicialRowLeftMultiplication
public import SerrePositivity.KST.ProExcision.OppositeVectorMultiplication
public import SerrePositivity.KST.ProExcision.SimplicialColumnRightMultiplication

/-!
# 実半直積比較と指定元の乗法の可換正方形

概要：反対係数での列の右乗法と元の行の左乗法を実単体的に比較する。
方針：基底成分は恒等、ファイバー成分は実核イデアルの反対乗法公式を用いる。
規約：KST Proposition 4.14、SW92 §1.2。中心性を仮定しない比較。
使われ方：行側の低次相対零化の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実反対転置の半直積同型は列の右乗法と行の左乗法に可換。
方針：全次数の実比較で基底とファイバーを別々に評価する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：零化を行側へ移す実正方形。 -/
lemma NonUnitalSimplicialRing.reverseOppositeAffineIso_multiplication
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n : ℕ) :
    simplicialActionProductMap (I.reverseOpposite.columnRightActionHom (MulOpposite.op a) n) ≫
        (I.reverseOppositeAffineIso n).hom =
      (I.reverseOppositeAffineIso n).hom ≫ monoidReverseOppositeMap (I.rowAffineLeftMap a n) := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply MulOpposite.unop_injective
  apply MulOpposite.unop_injective
  apply ActionProduct.ext
  · rfl
  · change integerUnitizationIdealOpVectorMulEquiv (I.obj k) n
        (idealVectorRightHom (integerUnitizationIdeal (I.obj k)ᵐᵒᵖ) (Fin n)
          (I.reverseOpposite.standardIdeal.vertexElement
            (I.reverseOpposite.standardElement (MulOpposite.op a)) k).val x.fiber) =
      idealVectorLeftHom (integerUnitizationIdeal (I.obj k)) (Fin n)
        (I.standardIdeal.vertexElement (I.standardElement a) k).val
        (integerUnitizationIdealOpVectorMulEquiv (I.obj k) n x.fiber)
    rw [integerUnitizationIdealOpVector_right_left, I.reverseOppositeStandardVertex]

end SerrePositivity.KST.ProExcision
