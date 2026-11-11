module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SmallDiagramComma

/-!
概要：小さい表示添字の各頂点評価と元の標準全余錐を照合する。
方針：元の実比較同型を全評価へ合成し、射影と全余錐の等式を保つ。
規約：cofinal 性は未主張。使われ方：有限半順序図式の各点密度への接続。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) (k : K _⦋0⦌)

/-- 同じ小さい添字の持ち上げから、元の指定値の実 comma への評価。 -/
def smallDiagramCommaEvaluation : (SSet.uliftFunctor.{u + 1, u}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ D) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D k

/-- 元の C の図式の同じ頂点での評価を厳密に回収する。 -/
lemma smallDiagramCommaEvaluation_projection : smallDiagramCommaEvaluation κ D k ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaProjection κ D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k) := by
  rw [smallDiagramCommaEvaluation, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation_projection,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso_projection, ← Functor.map_comp]

/-- 小さい標準全余錐の評価は、元の scalar 標準全余錐の同じ評価による制限。 -/
lemma smallDiagramCommaEvaluation_coconeMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (smallDiagramCommaEvaluation κ D k) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
        (D.app (Opposite.op ⦋0⦌) (ULift.up k))).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone κ D).val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) (ULift.up k) := by
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaIso κ D).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D k)
    (𝟙 (Δ[0] : SSet.{u + 1})) (𝟙 (Δ[0] : SSet.{u + 1}))
  simp only [Category.id_comp] at hj
  rw [smallDiagramCommaEvaluation, hj, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation_coconeMap, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
