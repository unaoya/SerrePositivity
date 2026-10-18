module
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# 単体の順序反転と連結成分の実比較

概要：単体的集合の順序反転は連結成分を自然な実全単射で保つ。
方針：辺の向きを逆転し、同じ零次の代表で商への写像を構成する。
規約：KST Proposition 4.14 の反転した係数環の π₀ の比較。
使われ方：非可換な行側 ĜL の成分での可逆性の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：順序反転した単体的集合の辺を逆向きの元の辺へ移す。
方針：二つの零次の面が入れ替わることを使う。
規約：KST Proposition 4.14。使われ方：π₀ の商写像の代表独立性。 -/
def reversalEdge {X : SSet.{u}} {a b : X.op _⦋0⦌} (e : X.op.Edge a b) :
    X.Edge (SSet.opObjEquiv (X := X) b) (SSet.opObjEquiv (X := X) a) :=
  .mk (SSet.opObjEquiv (X := X) e.edge)
    (by
      have h := congrArg (SSet.opObjEquiv (X := X)) e.tgt_eq
      simpa only [SSet.op_δ, Equiv.apply_symm_apply, show (0 : Fin 2).rev = 1 from rfl] using h)
    (by
      have h := congrArg (SSet.opObjEquiv (X := X)) e.src_eq
      simpa only [SSet.op_δ, Equiv.apply_symm_apply, show (1 : Fin 2).rev = 0 from rfl] using h)

/-- 概要：元の単体的集合の辺を逆向きの反転した辺へ移す。
方針：反転した二つの面に元の両端の式を適用する。
規約：KST Proposition 4.14。使われ方：π₀ の反転比較の逆写像。 -/
def edgeToReversal {X : SSet.{u}} {a b : X _⦋0⦌} (e : X.Edge a b) :
    X.op.Edge ((SSet.opObjEquiv (X := X)).symm b) ((SSet.opObjEquiv (X := X)).symm a) :=
  .mk ((SSet.opObjEquiv (X := X)).symm e.edge)
    (by
      change X.op.δ 1 ((SSet.opObjEquiv (X := X)).symm e.edge) = _
      simp only [SSet.op_δ, Equiv.apply_symm_apply,
        show (0 : Fin 2).rev = 1 from rfl, show (1 : Fin 2).rev = 0 from rfl]
      exact congrArg (SSet.opObjEquiv (X := X)).symm e.tgt_eq)
    (by
      change X.op.δ 0 ((SSet.opObjEquiv (X := X)).symm e.edge) = _
      simp only [SSet.op_δ, Equiv.apply_symm_apply,
        show (0 : Fin 2).rev = 1 from rfl, show (1 : Fin 2).rev = 0 from rfl]
      exact congrArg (SSet.opObjEquiv (X := X)).symm e.src_eq)

/-- 概要：反転した単体的集合の連結成分から元の連結成分への実写像。
方針：零次の代表を保ち、辺の向きを反転して商へ降ろす。
規約：KST Proposition 4.14。使われ方：反転した環の成分の比較。 -/
def reversalComponentsMap (X : SSet.{u}) : π₀ X.op → π₀ X :=
  π₀.lift (fun a ↦ π₀.mk (SSet.opObjEquiv (X := X) a))
    (fun _ _ e ↦ (π₀.sound (reversalEdge e)).symm)

/-- 概要：単体の順序反転は連結成分を実全単射で保つ。
方針：両方向の辺の逆転で商の写像を構成し、零次の代表で互いの逆を検証する。
規約：KST Proposition 4.14、π₀ は Mathlib の商。
使われ方：成分環の反転比較の台となる全単射。 -/
def reversalComponentsEquiv (X : SSet.{u}) : π₀ X.op ≃ π₀ X where
  toFun := reversalComponentsMap X
  invFun := π₀.lift (fun a ↦ π₀.mk ((SSet.opObjEquiv (X := X)).symm a))
    (fun _ _ e ↦ (π₀.sound (edgeToReversal e)).symm)
  left_inv x := by induction x using π₀.rec with | mk a => rfl
  right_inv x := by induction x using π₀.rec with | mk a => rfl

end SerrePositivity.KST.ProExcision
