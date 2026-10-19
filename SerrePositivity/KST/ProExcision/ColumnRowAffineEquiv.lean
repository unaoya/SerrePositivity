module
public import SerrePositivity.KST.ProExcision.SimplicialRowAffine
public import SerrePositivity.KST.ProExcision.ActionProductEquiv
public import SerrePositivity.KST.ProExcision.OppositeColumnRowEquivariance
public import SerrePositivity.KST.ProExcision.HatGLReverseOppositeIso

/-!
# 反対転置による列側・行側半直積の実乗法同型

概要：反転した反対係数の列側半直積を元の行側の反対半直積に同定する。
方針：実 ĜL 同型と実核イデアル同型を、実証明した同変性に沿って合成する。
規約：KST Proposition 4.14、SW92 §1.2。係数方向の rev と乗法方向の op を含める。
使われ方：行側への実相対零化の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：反対係数の列側半直積と元の右行列作用の左半直積の実同型。
方針：基底の実反対転置とファイバーの実加法同型に同変性を適用する。
規約：SW92 §1.2。使われ方：行側全体の比較の各次数。 -/
def NonUnitalSimplicialRing.reverseOppositeColumnRowMulEquiv
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ) :
    (simplicialActionProduct (I.reverseOpposite.hatGLColumnAction n)).obj (op ⦋q⦌) ≃*
      (simplicialActionProduct (I.hatGLRowAction n)).obj (op ⦋q⦌) := by
  letI := (I.reverseOpposite.hatGLColumnAction n).actionStructure (op ⦋q⦌)
  letI := (I.hatGLRowAction n).actionStructure (op ⦋q⦌)
  exact actionProductMulEquiv (I.reverseOppositeHatGLMulEquiv n q)
    (integerUnitizationIdealOpVectorMulEquiv (I.obj (op ⦋q⦌)) n)
    (fun A v ↦ integerUnitizationIdealOpVector_equivariant (I.obj (op ⦋q⦌)) n A.val v)

/-- 概要：列側半直積と係数反転した行側の反対モノイドの実同型。
方針：実同変な半直積同型と二重反対モノイドの実同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：対角全体の bar 反転同型への接続。 -/
def NonUnitalSimplicialRing.reverseOppositeAffineMulEquiv
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ) :
    (simplicialActionProduct (I.reverseOpposite.hatGLColumnAction n)).obj (op ⦋q⦌) ≃*
      (monoidReverseOpposite (I.rowAffine n)).obj (op ⦋q⦌) :=
  (I.reverseOppositeColumnRowMulEquiv n q).trans (MulEquiv.opOp _)

end SerrePositivity.KST.ProExcision
