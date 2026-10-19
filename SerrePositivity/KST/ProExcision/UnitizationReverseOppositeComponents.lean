module
public import SerrePositivity.KST.ProExcision.UnitizationOppositeDiagram
public import SerrePositivity.KST.ProExcision.ComponentRingSimplex

/-!
# 反転した反対非単位環の単位化の成分環

概要：rev と反対環を施した非単位単体環の単位化の成分環を元の成分環の反対環へ送る。
方針：単位化図式の実同型、反対成分環の実同型、rev の実成分環同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2 の行側の実係数比較。
使われ方：転置を伴う実 ĜL の単位条件の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：rev と反対環を施した標準単位化の成分環の実環同型。
方針：三つの証明済みの実成分環同型を合成する。
規約：KST Proposition 4.14、非可換な積の順序逆転は反対環に明示する。
使われ方：反転した係数環上の行列の成分での単位性。 -/
def NonUnitalSimplicialRing.reverseOppositeComponentEquiv (I : NonUnitalSimplicialRing.{u}) :
    π₀ (Comparison.ringSpace I.reverseOpposite.standardIdeal.ambient) ≃+*
      (π₀ (Comparison.ringSpace I.standardIdeal.ambient))ᵐᵒᵖ :=
  (componentRingEquiv I.unitizationReverseOppositeIso).trans
    ((ringOppositeComponentsEquiv (SimplicialObject.opFunctor.obj I.standardIdeal.ambient)).trans
      (RingEquiv.op (ringReversalComponentsEquiv I.standardIdeal.ambient)))

/-- 概要：反転した反対環の成分環比較は任意の次数の成分写像と可換。
方針：三つの実同型の成分に関する自然性を順に適用する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：実転置で送った行列の可逆性の証明。 -/
lemma NonUnitalSimplicialRing.reverseOppositeComponentEquiv_simplex
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ)
    (x : Unitization ℤ (I.obj (op ⦋n⦌))ᵐᵒᵖ) :
    I.reverseOppositeComponentEquiv
      (Comparison.SimplicialRing.simplexToComponents I.reverseOpposite.standardIdeal.ambient n x) =
      MulOpposite.op (Comparison.SimplicialRing.simplexToComponents I.standardIdeal.ambient n
        (MulOpposite.unop (integerUnitizationOpEquiv (I.obj (op ⦋n⦌)) x))) := by
  change (RingEquiv.op (ringReversalComponentsEquiv I.standardIdeal.ambient))
    (ringOppositeComponentsEquiv _
      (componentRingEquiv I.unitizationReverseOppositeIso
        (Comparison.SimplicialRing.simplexToComponents I.reverseOpposite.standardIdeal.ambient n x))) = _
  rw [componentRingEquiv_simplex, ringOppositeComponentsEquiv_simplex]
  change MulOpposite.op (ringReversalComponentsEquiv I.standardIdeal.ambient
      (Comparison.SimplicialRing.simplexToComponents
        (SimplicialObject.opFunctor.obj I.standardIdeal.ambient) n
        (MulOpposite.unop (integerUnitizationOpEquiv (I.obj (op ⦋n⦌)) x)))) = _
  exact congrArg MulOpposite.op
    (ringReversalComponentsEquiv_simplex I.standardIdeal.ambient n
      (MulOpposite.unop (integerUnitizationOpEquiv (I.obj (op ⦋n⦌)) x)))

end SerrePositivity.KST.ProExcision
