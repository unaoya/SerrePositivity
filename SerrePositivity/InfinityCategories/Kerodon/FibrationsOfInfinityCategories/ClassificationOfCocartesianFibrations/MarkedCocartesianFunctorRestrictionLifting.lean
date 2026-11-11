module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PredicateIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreIsofibration

/-!
概要：指定辺を保つ相対 Hom の単射による制限の同値持ち上げと core の Kan 充填性。
方針：指定辺の保存条件の同型不変性で、元の全相対 Hom の持ち上げを制限する。
規約：始域の辺の指定は任意で、制限する単射の同値性を要求しない。
使われ方：各底変換上の元の Hom の core のセルによる貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定辺の cocartesian 性は、同じ相対関手空間の頂点の同型で不変。 -/
lemma markedCocartesianFunctorPredicate_iff_of_vertexIso {A E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [InnerFibration q] (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a) _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a W v ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a W w := by
  let : Quasicategory E := quasicategory_of_innerFibration q
  obtain ⟨f, hf, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q a v
  obtain ⟨g, hg, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q a w
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex]
  exact forall_congr' (fun e ↦ imp_congr_right (fun _ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_of_functorIso q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex_functorIso q a hf hg h) e))

/-- 指定辺を保つ Hom の単射による制限は、単射な前合成同値の相対持ち上げを持つ。 -/
lemma kanEquivalenceLifting_markedCocartesianFunctorPre {E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left]
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi) := by
  intro K L j hj he
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.kanEquivalenceLifting_fullRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q b.hom W)
    (fun h ↦ markedCocartesianFunctorPredicate_iff_of_vertexIso q b.hom W h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a.hom V) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q i V W hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian q i) j hj he

/-- 同じ指定辺を保つ Hom の core の単射による制限は Kan fibration。 -/
lemma core_markedCocartesianFunctorPre_fibration {E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left]
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_markedCocartesianFunctorPre q i V W hi)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
