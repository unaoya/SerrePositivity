module
public import SerrePositivity.KST.ProExcision.MonoidOpposite
public import SerrePositivity.KST.ProExcision.IdealRowMatrixAction
public import SerrePositivity.KST.ProExcision.TriangularAffineHatGL

/-!
# 実 ĜL の行ベクトルへの右作用と行側半直積

概要：右行列作用を反対 ĜL の左作用として束ね、実行側半直積を構成する。
方針：係数自然性と反対モノイドを用いて積の順序を保つ。
規約：KST Proposition 4.14、SW92 §1.2。係数の可換性を仮定しない。
使われ方：行側の実相対ホモロジーの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：反対 ĜL のイデアル内の行ベクトルへの実左作用。
方針：実右行列作用を反対 ĜL の実表現へ制限する。
規約：SW92 §1.2、右行列作用を反対乗法で表す。
使われ方：実行側半直積の係数方向の構成。 -/
def NonUnitalSimplicialRing.hatGLRowAction (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    SimplicialMonoidAction (monoidOpposite (I.hatGL n))
      (I.standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat) where
  action k := (idealRowMatrixAction n (I.standardIdeal.ideal k)).comp
    (MonoidHom.op (I.hatGLSubmonoid n k.unop.len).subtype)
  naturality {k l} f M v :=
    idealRowMatrixAction_functorial n (I.standardIdeal.ideal k) (I.standardIdeal.ideal l)
      (I.standardIdeal.ambient.map f).hom (I.standardIdeal.map_mem f)
      (MulOpposite.op (MulOpposite.unop M).val) v

/-- 概要：実 ĜL とイデアル内の行ベクトルの右作用による実半直積。
方針：反対 ĜL の左作用半直積の乗法を反転する。
規約：SW92 §1.2、積の行成分は v h+w。加法は可換、係数乗法は非可換。
使われ方：列側零化の反対転置による移送の値域。 -/
def NonUnitalSimplicialRing.rowAffine (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    SimplicialObject MonCat.{u} :=
  monoidOpposite (simplicialActionProduct (I.hatGLRowAction n))

/-- 概要：実行側半直積の基底成分。
方針：反対型を二回外す。
規約：SW92 §1.2。使われ方：実アフィン埋め込みの行列成分。 -/
def NonUnitalSimplicialRing.rowAffineBase
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ)
    (x : (I.rowAffine n).obj (op ⦋q⦌)) : I.hatGLSubmonoid n q :=
  MulOpposite.unop (MulOpposite.unop x).base

/-- 概要：実行側半直積の行ベクトル成分。
方針：反対半直積の群成分を実核イデアル内の行として読む。
規約：SW92 §1.2。使われ方：実行列による計算の型を明示する。 -/
def NonUnitalSimplicialRing.rowAffineFiber
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ)
    (x : (I.rowAffine n).obj (op ⦋q⦌)) :
    Multiplicative (Fin n → integerUnitizationIdeal (I.obj (op ⦋q⦌))) :=
  (MulOpposite.unop x).fiber

/-- 概要：実行側半直積の行成分の乗法公式。
方針：反対半直積の積を展開し、行群の加法の交換法則を使う。
規約：SW92 §1.2、右作用の順序 v h+w。
使われ方：実行列へのアフィン埋め込みと共役の計算。 -/
lemma NonUnitalSimplicialRing.rowAffine_mul_fiber
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ)
    (x y : (I.rowAffine n).obj (op ⦋q⦌)) (j : Fin n) :
    ((I.rowAffineFiber n q (x * y)).toAdd j : Unitization ℤ (I.obj (op ⦋q⦌))) =
      (∑ i, ((I.rowAffineFiber n q x).toAdd i : Unitization ℤ (I.obj (op ⦋q⦌))) *
        (I.rowAffineBase n q y).val i j) +
          ((I.rowAffineFiber n q y).toAdd j : Unitization ℤ (I.obj (op ⦋q⦌))) := by
  change ((I.rowAffineFiber n q y).toAdd j : Unitization ℤ (I.obj (op ⦋q⦌))) +
      (∑ i, ((I.rowAffineFiber n q x).toAdd i : Unitization ℤ (I.obj (op ⦋q⦌))) *
        (I.rowAffineBase n q y).val i j) = _
  exact add_comm _ _

end SerrePositivity.KST.ProExcision
