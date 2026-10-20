module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationCoslicePointFamily
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：coslice 全体上の相対関手の比較を、恒等錐での評価から回収する。
方針：正規化した評価の自明 Kan 性を使い、その同じ評価の逆で二胞体を戻す。
規約：パラメーターは任意の単体集合。比較は相対関手空間全体の関手同型である。
使われ方：恒等点から作った大域比較を、同じ始点を持つ輸送の族と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等錐での評価後の比較を、任意の全パラメーターで大域的な相対関手へ戻す。 -/
def leftFibrationCoslicePointEvaluate_reflectIso
    {E B P : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (b : B _⦋0⦌)
    {f g : P ⟶ relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b))}
    (h : FunctorIso (f ≫ leftFibrationCoslicePointEvaluate p b)
      (g ≫ leftFibrationCoslicePointEvaluate p b)) : FunctorIso f g := by
  have : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  have := leftFibrationCoslicePointEvaluate_trivialKanFibration p b
  let e := (isQCatEquivalence_of_trivialKanFibration
    (leftFibrationCoslicePointEvaluate p b)).choose
  exact (FunctorIso.precomp e.homInvIso f).symm ≪≫
    FunctorIso.postcomp h e.inv ≪≫ FunctorIso.precomp e.homInvIso g

/-- 同じ恒等錐での値を持つ二つの大域的な族は、相対関手空間で同型。 -/
def leftFibrationCoslicePointEvaluate_equalIso
    {E B P : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (b : B _⦋0⦌)
    {f g : P ⟶ relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b))}
    (h : f ≫ leftFibrationCoslicePointEvaluate p b =
      g ≫ leftFibrationCoslicePointEvaluate p b) : FunctorIso f g :=
  leftFibrationCoslicePointEvaluate_reflectIso p b
    (eqToIso (congrArg (fun k ↦ SSet.HomotopyCategory.mk (functorVertex k)) h))

/-- 任意の大域的な族は、恒等錐で評価して同じ標準切断で戻した族と同型。 -/
def leftFibrationCoslicePointSection_recoveryIso
    {E B P : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (b : B _⦋0⦌)
    (f : P ⟶ relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm b))) :
    FunctorIso (f ≫ leftFibrationCoslicePointEvaluate p b ≫
      leftFibrationCoslicePointSection p b) f := by
  apply leftFibrationCoslicePointEvaluate_equalIso p b
  simp only [Category.assoc, leftFibrationCoslicePointSection_evaluate, Category.comp_id]

end SerrePositivity.InfinityCategories
