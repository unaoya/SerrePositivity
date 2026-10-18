module

public import SerrePositivity.InfinityCategories.F1.CoherentResolutionArrowEnriched

/-!
概要：解像への標準比較を coherent な空間値関手の族として実現する。
方針：二点の図式への豊穣関手に coherent nerve と共同評価を適用する。
規約：族の始点と終点は単体集合の射の厳密な等式で計算する。
使われ方：Kerodon Corollary 5.6.0.6、対象ごとの比較を図式全体へ移すための高次の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 複体の解像の豊穣自己関手が空間の coherent nerve に誘導する写像。
方針：解像の豊穣自己関手へ coherent nerve を適用する。
規約：全ての高次単体の射へ作用する。
使われ方：Kerodon Proposition 4.6.7.16、coherent な図式の自然な置換の終点。 -/
noncomputable def coherentResolutionInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  coherentNerveMap coherentResolutionKanEnriched

/-- 概要：解像への標準比較を二点の底上の coherent な空間値図式の族にする。
方針：二点の図式の豊穣的な族を共同評価で実現する。
規約：始域は空間の coherent nerve、関手の底は二点の順序の nerve の宇宙持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6、任意の coherent な図式に引き戻せる比較の族。 -/
noncomputable def coherentResolutionComparisonFamily :
    SpaceInfinity.{u} ⟶ SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2)))) :=
  coherentNerveMap coherentResolutionArrowEnriched ≫ kanDiagramRealization _

/-- 概要：標準比較の coherent な族を始点で評価すると恒等写像になる。
方針：共同評価の対象ごとの公式と豊穣関手の始点の等式を使う。
規約：始点は二重に持ち上げた零の頂点。
使われ方：Kerodon Corollary 5.6.0.6、解像への大域的な比較の始点条件。 -/
lemma coherentResolutionComparisonFamily_zero :
    coherentResolutionComparisonFamily.{u} ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) =
        𝟙 SpaceInfinity.{u} := by
  rw [coherentResolutionComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  change coherentNerveMap coherentResolutionArrowEnriched ≫
    coherentNerveMap (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = _
  rw [← coherentNerveMap_comp, coherentResolutionArrowEnriched_zero, coherentNerveMap_id]
  rfl

/-- 概要：標準比較の coherent な族を終点で評価すると解像の自己写像になる。
方針：共同評価の対象ごとの公式と豊穣関手の終点の等式を使う。
規約：終点は二重に持ち上げた一の頂点。
使われ方：Kerodon Corollary 5.6.0.6、解像への大域的な比較の終点条件。 -/
lemma coherentResolutionComparisonFamily_one :
    coherentResolutionComparisonFamily.{u} ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) =
        coherentResolutionInfinityMap.{u} := by
  rw [coherentResolutionComparisonFamily, Category.assoc, kanDiagramRealization_evaluate]
  change coherentNerveMap coherentResolutionArrowEnriched ≫
    coherentNerveMap (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = _
  rw [← coherentNerveMap_comp, coherentResolutionArrowEnriched_one]
  rfl

end SerrePositivity.InfinityCategories
