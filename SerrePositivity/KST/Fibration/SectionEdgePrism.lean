module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreLift
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Transport

/-! # 元の section の全族を指定した辺で評価する厳密な prism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ全 section を、指定した始域の実辺に沿って同時に評価する。 -/
def sectionEdgePrism {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (e : Δ[1] ⟶ A) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a ⟶ E :=
  uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre e).app E)

/-- 元の両端評価は、全 section 上の同じ prism の端点そのもの。 -/
theorem sectionEdgePrism_endpoint {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (e : Δ[1] ⟶ A) (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint j _ ≫ sectionEdgePrism p a e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p a
        (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) := by
  rw [sectionEdgePrism, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]

/-- 同じ prism を底へ送ると、指定辺の底像の定値パラメータ族となる。 -/
theorem sectionEdgePrism_projection {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (e : Δ[1] ⟶ A) :
    sectionEdgePrism p a e ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ e ≫ a := by
  unfold sectionEdgePrism
  rw [← uncurry_natural_right]
  have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre e).app E) ≫
        (ihom (Δ[1] : SSet.{u})).map p =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ a)) := by
    rw [Category.assoc, Category.assoc, ← (pre e).naturality p,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.const_comp, SSet.comp_const]
    rfl
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.KST.Fibration
