module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
/-!
概要：標的への像を固定した実可逆円柱を、相対関手空間内の頂点同型へ移す。
方針：元の全円柱の両端と評価の固定条件を、そのまま実際の射で回収する。
規約：標的の固定 fiber の充填性を追加仮定にしない。
使われ方：指定始点評価の下での全余錐比較の相対反映。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：標的全図式を固定した実可逆円柱は、相対関手空間内の頂点同型を与える。
方針：可逆区間の両頂点の同型を写す。規約：全射を保持。使われ方：相対反映。 -/
lemma nonempty_relativeFunctorVertexIso_of_equivalenceCylinder
    {A D E : SSet.{u}} (p : D ⟶ E) (a : A ⟶ E)
    (f g : A ⟶ D) (hf : f ≫ p = a) (hg : g ≫ p = a)
    (H : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ D)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false ≫ H = f)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true ≫ H = g)
    (hH : H ≫ p = fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ a) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a f hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a g hg)) := by
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry H hH
  let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up false))
  let y : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up true))
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isContractibleKan_codiscreteNerve (ULift.{u} Bool)
  have : KanComplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} := hc.kanComplex
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex x) (hc.isTerminalVertex y)
  have hx : M.app (Opposite.op ⦋0⦌) x = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a f hf := by
    apply Subtype.ext
    change (curry H).app (Opposite.op ⦋0⦌) x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorVertex_equivalenceCylinderEndpoint_uncurry (curry H) false
    rw [uncurry_curry, h₀] at h
    exact h.symm
  have hy : M.app (Opposite.op ⦋0⦌) y = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a g hg := by
    apply Subtype.ext
    change (curry H).app (Opposite.op ⦋0⦌) y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorVertex_equivalenceCylinderEndpoint_uncurry (curry H) true
    rw [uncurry_curry, h₁] at h
    exact h.symm
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hx)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e M ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hy)⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
