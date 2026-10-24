module

public import SerrePositivity.InfinityCategories.F2.Presentable.YonedaWeightLeftKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomWeightEvaluationFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaHomWeightRestriction

/-!
概要：元の全 Yoneda 自然変換空間族と、元の全係数前層評価族を全自然同型で比較する。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：元の全係数で制限した Yoneda Hom 関手の転置は、同じ全自然変換空間族そのもの。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。 -/
lemma yonedaHomWeightFamily_transpose
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    transposeFunctorFamily
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀) ≫
        presheafHomWeightDiagram (yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C))) =
      yonedaHomWeightFamily F₀ := by
  simp only [transposeFunctorFamily_comp, yonedaHomWeightFamily]
  dsimp only [transposeFunctorFamily]
  erw [presheafHomWeightDiagram_transpose]
  rw [Category.assoc]

/-- 概要：元の全 Yoneda 自然変換空間族は、全係数前層評価族と両変数で自然同型。
方針：全前層 Yoneda 評価比較を元の全係数へ制限し、二変数交換で全族に戻す。
規約：全 C・全標的係数・元の Hom 係数関手を保持する。
使われ方：P_Σ 延長の二つの右 Kan 族の制限同型。 -/
def yonedaHomWeightFamily_evaluationIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    FunctorIso (yonedaHomWeightFamily F₀) (homWeightEvaluationFamily F₀) := by
  have e := FunctorIso.transpose
    ((yonedaHomWeightDiagram_universeIso ((SSet.uliftFunctor.{u + 1, u}).obj C)).precomp
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀)))
  rw [yonedaHomWeightFamily_transpose] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
