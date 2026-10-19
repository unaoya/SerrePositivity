module
public import SerrePositivity.KST.ProExcision.HatGLReverseOppositeMatrix

/-!
# 反転した反対係数環の ĜL の実乗法同型

概要：整数核と成分での可逆性を保つ反対転置を、部分モノイドの実乗法同型にする。
方針：周囲の行列環の実同型を、両方向の所属条件によって制限する。
規約：KST Proposition 4.14、SW92 §1.2。非可換環に可換性を課さない。
使われ方：列側と行側の単体的モノイドの比較の各次数。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：反転した反対係数環の ĜL と元の ĜL の反対モノイドの実乗法同型。
方針：反対転置の実環同型と所属条件の同値を用いて互いに逆な写像を作る。
規約：KST Proposition 4.14、SW92 §1.2。各次数での逆行列は仮定しない。
使われ方：非可換な行側比較の自然同型の各成分。 -/
def NonUnitalSimplicialRing.reverseOppositeHatGLMulEquiv
    (I : NonUnitalSimplicialRing.{u}) (n q : ℕ) :
    I.reverseOpposite.hatGLSubmonoid n q ≃* (I.hatGLSubmonoid n q)ᵐᵒᵖ where
  toFun A := MulOpposite.op ⟨MulOpposite.unop
    (integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n A.val),
      (I.reverseOppositeHatGL_mem_iff n q A.val).mp A.property⟩
  invFun B := ⟨(integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n).symm
    (MulOpposite.op (MulOpposite.unop B).val), by
      apply (I.reverseOppositeHatGL_mem_iff n q _).mpr
      simpa only [RingEquiv.apply_symm_apply, MulOpposite.unop_op] using
        (MulOpposite.unop B).property⟩
  left_inv A := by
    apply Subtype.ext
    exact (integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n).symm_apply_apply A.val
  right_inv B := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact congrArg MulOpposite.unop
      ((integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n).apply_symm_apply
        (MulOpposite.op (MulOpposite.unop B).val))
  map_mul' A B := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact congrArg MulOpposite.unop
      ((integerUnitizationMatrixOpEquiv (I.obj (op ⦋q⦌)) n).map_mul A.val B.val)

end SerrePositivity.KST.ProExcision
