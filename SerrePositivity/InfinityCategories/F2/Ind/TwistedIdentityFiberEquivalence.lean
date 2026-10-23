module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedIdentityFiber
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseLeftFilling
public import SerrePositivity.InfinityCategories.F1B.WeakHomotopy

/-!
概要：同じ大域評価の恒等射上の fiber 作用そのものは同値。
方針：Kan fiber の左右の射影の自明 Kan 性と、右端の厳密な切断条件を使う。
規約：切断を選び直さず、元の大域切断の同じ制限を判定する。
使われ方：指定密度余錐の各評価の弱同値性の初期値。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌)

local instance : KanComplex (vertexFiber p b) := vertexFiber_kanComplex p b

/-- 同じ元の大域評価を恒等点に制限した作用自身は、元の Kan fiber の同値。 -/
lemma twistedIdentityFiberEvaluation_isQCatEquivalence :
    IsQCatEquivalence (twistedIdentityFiberEvaluation p b) := by
  have hR := isQCatEquivalence_of_trivialKanFibration (edgewiseRight (vertexFiber p b))
  have hS : IsQCatEquivalence (twistedIdentityFiberLift p b) := hR.cancel_right (by
    rw [twistedIdentityFiberLift_right]
    exact (QCatEquivalence.refl _).isQCatEquivalence)
  exact hS.comp (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (vertexFiber p b)))

/-- 同じ恒等点評価は、元の fiber からその反転への弱ホモトピー同値でもある。 -/
lemma twistedIdentityFiberEvaluation_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (twistedIdentityFiberEvaluation p b) :=
  (twistedIdentityFiberEvaluation_isQCatEquivalence p b).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
