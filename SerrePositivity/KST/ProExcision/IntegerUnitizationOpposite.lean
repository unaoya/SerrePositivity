module
public import SerrePositivity.KST.ProExcision.IntegerUnitizationMap
public import Mathlib.Algebra.Ring.Opposite

/-!
# 整数単位化と反対環の実比較

概要：非単位環の反対環の整数単位化を、整数単位化の反対環と実同型で比較する。
方針：整数成分を保ち、非単位環の成分を unop して反対環へ入れる。
規約：KST Proposition 4.14、SW92 Proposition 1.5 の行側比較。非可換な転置を環準同型と混同しない。
使われ方：列側と行側のアフィン比較を反対環で結び付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open MulOpposite
variable (I : Type u) [NonUnitalRing I]

/-- 概要：反対環の整数単位化と整数単位化の反対環の実環同型。
方針：二つの成分を保つ全単射に、積の順序反転を伴う乗法保存を示す。
規約：KST Proposition 4.14、SW92 §1.2 の反対環の比較。
使われ方：行側の実アフィン比較の周囲環の同定。 -/
def integerUnitizationOpEquiv : Unitization ℤ Iᵐᵒᵖ ≃+* (Unitization ℤ I)ᵐᵒᵖ where
  toFun x := op ⟨(x.fst, unop x.snd)⟩
  invFun x := ⟨((unop x).fst, op (unop x).snd)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_mul' x y := by
    apply unop_injective
    apply Unitization.ext
    · change x.fst * y.fst = y.fst * x.fst
      exact mul_comm _ _
    · change unop (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) =
        y.fst • unop x.snd + x.fst • unop y.snd + unop y.snd * unop x.snd
      simp only [unop_add, unop_mul]
      change x.fst • unop y.snd + y.fst • unop x.snd + unop y.snd * unop x.snd = _
      rw [add_comm (x.fst • unop y.snd) (y.fst • unop x.snd)]

/-- 概要：反対環との比較は整数成分を保つ。
方針：実同型の第一成分を評価する。
規約：KST Proposition 4.14。使われ方：非単位環の ĜL の整数核条件の保存。 -/
lemma integerUnitizationOpEquiv_fst (x : Unitization ℤ Iᵐᵒᵖ) :
    (unop (integerUnitizationOpEquiv I x)).fst = x.fst := rfl

/-- 概要：反対環との比較は元の非単位環の包含を保つ。
方針：実同型の第二成分を評価する。
規約：KST Proposition 4.14。使われ方：列と行の係数イデアルの比較。 -/
lemma integerUnitizationOpEquiv_inr (x : Iᵐᵒᵖ) :
    integerUnitizationOpEquiv I (x : Unitization ℤ Iᵐᵒᵖ) = op ((unop x : I) : Unitization ℤ I) := rfl

end SerrePositivity.KST.ProExcision
