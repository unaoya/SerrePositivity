module
public import SerrePositivity.KST.ProExcision.UnitizationReverseOppositeComponents
public import SerrePositivity.KST.ProExcision.NonUnitalHatGL
public import Mathlib.Algebra.Group.Units.Opposite

/-!
# 反転した反対係数環の行列と ĜL の実比較

概要：単位化の反対環同型と非可換な転置を合成し、成分での単位条件と整数核条件を比較する。
方針：実行列の環同型と実成分行列の環同型の可換性を各成分で証明する。
規約：KST Proposition 4.14、SW92 §1.2。転置の順序逆転は反対環に明示する。
使われ方：行側の実一般線形モノイドと列側の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：非単位環の反対単位化上の行列を元の単位化上の反対行列環へ送る実環同型。
方針：整数単位化の実反対環同型と非可換な転置同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：反転した反対 ĜL の各次数の実行列比較。 -/
def integerUnitizationMatrixOpEquiv (J : Type u) [NonUnitalRing J] (n : ℕ) :
    Matrix (Fin n) (Fin n) (Unitization ℤ Jᵐᵒᵖ) ≃+*
      (Matrix (Fin n) (Fin n) (Unitization ℤ J))ᵐᵒᵖ :=
  (integerUnitizationOpEquiv J).mapMatrix.trans RingEquiv.mopMatrix

/-- 概要：実反対転置の整数成分は元の整数成分行列の転置。
方針：各成分で整数単位化の実同型の第一成分を評価する。
規約：KST Proposition 4.14。使われ方：非単位 ĜL の整数核条件の両方向の保存。 -/
lemma integerUnitizationMatrixOpEquiv_fst (J : Type u) [NonUnitalRing J] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ Jᵐᵒᵖ)) :
    (Unitization.fstHom ℤ J).mapMatrix (MulOpposite.unop (integerUnitizationMatrixOpEquiv J n A)) =
      ((Unitization.fstHom ℤ Jᵐᵒᵖ).mapMatrix A).transpose := by
  apply Matrix.ext
  intro i j
  rfl

/-- 概要：反転した反対係数環の成分行列環の実同型。
方針：実成分環同型と非可換な転置を合成する。
規約：KST Proposition 4.14。使われ方：実成分行列の単位性の保存。 -/
def NonUnitalSimplicialRing.reverseOppositeMatrixComponentsEquiv
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    Matrix (Fin n) (Fin n) (π₀ (Comparison.ringSpace I.reverseOpposite.standardIdeal.ambient)) ≃+*
      (Matrix (Fin n) (Fin n) (π₀ (Comparison.ringSpace I.standardIdeal.ambient)))ᵐᵒᵖ :=
  I.reverseOppositeComponentEquiv.mapMatrix.trans RingEquiv.mopMatrix

/-- 概要：実反対転置と成分行列の二つの環同型は可換。
方針：行列の各成分に任意の次数の成分環の比較を適用する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：ĜL の成分での可逆性の両方向の移送。 -/
lemma NonUnitalSimplicialRing.reverseOppositeMatrix_components
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ (I.obj (op ⦋q⦌))ᵐᵒᵖ)) :
    I.reverseOppositeMatrixComponentsEquiv n
        (Comparison.matrixToComponents I.reverseOpposite.standardIdeal.ambient n q A) =
      MulOpposite.op (Comparison.matrixToComponents I.standardIdeal.ambient n q
        (MulOpposite.unop (integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n A))) := by
  apply MulOpposite.unop_injective
  apply Matrix.ext
  intro i j
  change MulOpposite.unop (I.reverseOppositeComponentEquiv
      (Comparison.SimplicialRing.simplexToComponents I.reverseOpposite.standardIdeal.ambient q (A j i))) =
    Comparison.SimplicialRing.simplexToComponents I.standardIdeal.ambient q
      (MulOpposite.unop (integerUnitizationOpEquiv (I.obj (op ⦋q⦌)) (A j i)))
  exact congrArg MulOpposite.unop (I.reverseOppositeComponentEquiv_simplex q (A j i))

/-- 概要：実反対転置は非単位 ĜL の条件を両方向に保存する。
方針：成分行列の実同型での単位性と整数射影の転置を比較する。
規約：KST Proposition 4.14、各次数での可逆性は要求しない。
使われ方：行側と列側の実一般線形モノイドの全単射。 -/
lemma NonUnitalSimplicialRing.reverseOppositeHatGL_mem_iff
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ (I.obj (op ⦋q⦌))ᵐᵒᵖ)) :
    A ∈ I.reverseOpposite.hatGLSubmonoid n q ↔
      MulOpposite.unop (integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n A) ∈
        I.hatGLSubmonoid n q := by
  constructor
  · intro h
    constructor
    · change IsUnit (Comparison.matrixToComponents I.standardIdeal.ambient n q _)
      have hu := h.1.map (I.reverseOppositeMatrixComponentsEquiv n).toMonoidHom
      change IsUnit (I.reverseOppositeMatrixComponentsEquiv n
        (Comparison.matrixToComponents I.reverseOpposite.standardIdeal.ambient n q A)) at hu
      rw [I.reverseOppositeMatrix_components] at hu
      exact hu.unop
    · have hf : (Unitization.fstHom ℤ (I.obj (op ⦋q⦌))ᵐᵒᵖ).mapMatrix A = 1 := h.2
      rw [integerUnitizationMatrixOpEquiv_fst, hf, Matrix.transpose_one]
  · intro h
    constructor
    · change IsUnit (Comparison.matrixToComponents I.reverseOpposite.standardIdeal.ambient n q A)
      have hu := h.1.op
      rw [← I.reverseOppositeMatrix_components] at hu
      have hv := hu.map (I.reverseOppositeMatrixComponentsEquiv n).symm.toMonoidHom
      change IsUnit ((I.reverseOppositeMatrixComponentsEquiv n).symm
        ((I.reverseOppositeMatrixComponentsEquiv n)
          (Comparison.matrixToComponents I.reverseOpposite.standardIdeal.ambient n q A))) at hv
      simpa only [RingEquiv.symm_apply_apply] using hv
    · change (Unitization.fstHom ℤ (I.obj (op ⦋q⦌))ᵐᵒᵖ).mapMatrix A = 1
      have hfst := h.2
      rw [integerUnitizationMatrixOpEquiv_fst] at hfst
      have he := congrArg Matrix.transpose hfst
      simpa only [Matrix.transpose_transpose, Matrix.transpose_one] using he

end SerrePositivity.KST.ProExcision
