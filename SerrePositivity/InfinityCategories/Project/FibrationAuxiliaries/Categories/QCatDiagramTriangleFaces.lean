module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatDiagramEdges

/-!
概要：元の二射の列の coherent 表示の二単体は、元の三辺を厳密に回収する。
方針：面との自然性と通常の nerve の三面の計算を使う。
規約：選んだ元の二射の列そのものを保持する。
使われ方：元の底変換比較の同じ三辺を持つ coherent な二単体の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) {a b c : C} (f : a ⟶ b) (g : b ⟶ c)

/-- 元の二射の列の coherent な二単体の最初の辺は、元の最初の射の辺。 -/
lemma qCatDiagramCoherentNerve_triangle_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ (2 : Fin 3) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋2⦌)
      (ULift.up (ComposableArrows.mk₂ f g))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).edge := by
  rw [← δ_naturality_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋1⦌)
    (ULift.up ((nerve C).δ (2 : Fin 3) (ComposableArrows.mk₂ f g))) = _
  rw [nerve.δ₂_mk₂_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.qCatDiagramCoherentNerve_edge F f

/-- 元の二射の列の coherent な二単体の次の辺は、元の次の射の辺。 -/
lemma qCatDiagramCoherentNerve_triangle_second :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ (0 : Fin 3) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋2⦌)
      (ULift.up (ComposableArrows.mk₂ f g))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map g)).edge := by
  rw [← δ_naturality_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋1⦌)
    (ULift.up ((nerve C).δ (0 : Fin 3) (ComposableArrows.mk₂ f g))) = _
  rw [nerve.δ₀_mk₂_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.qCatDiagramCoherentNerve_edge F g

/-- 元の二射の列の coherent な二単体の長辺は、同じ合成射の辺。 -/
lemma qCatDiagramCoherentNerve_triangle_long :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ (1 : Fin 3) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋2⦌)
      (ULift.up (ComposableArrows.mk₂ f g))) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map (f ≫ g))).edge := by
  rw [← δ_naturality_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve F).app (Opposite.op ⦋1⦌)
    (ULift.up ((nerve C).δ (1 : Fin 3) (ComposableArrows.mk₂ f g))) = _
  rw [nerve.δ₁_mk₂_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.qCatDiagramCoherentNerve_edge F (f ≫ g)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
