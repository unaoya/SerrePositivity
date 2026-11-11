module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeOverAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullRestrictionPullback
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreTrivialFibration

/-!
概要：指定辺を覆う単射な同値による、元の指定辺保存 Hom の自明 Kan 制限。
方針：各指定辺が制限先で回収できるので頂点条件を反映し、元の相対 Hom の自明 Kan 性を移す。
規約：指定辺を覆う条件を明示し、spine の長辺が覆われるとは仮定しない。
使われ方：高次内ホーンでの元の cocartesian Hom の制限同値。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定辺を全て覆う制限は、元の指定辺保存条件を反映する。 -/
lemma markedCocartesianFunctorPredicate_reflect_of_markCover
    {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B} (i : a ⟶ b)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q b.hom) _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a.hom V
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q b.hom W v := by
  obtain ⟨f, hf, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex q b.hom v
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex] at hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex]
  intro e he
  obtain ⟨d, hd, hde⟩ := hcover e he
  have h := hv d hd
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) (i.left.app (Opposite.op ⦋1⦌) d)) at h
  rwa [hde] at h

/-- 指定辺を覆う同じ単射な同値による、指定辺保存 Hom の制限は自明 Kan。 -/
lemma markedCocartesianFunctorPre_trivialKanFibration_of_markCover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i.left)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d ∈ W)
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_trivialKanFibration_of_cocartesian q i he
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.fullRestriction_trivialKanFibration _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_ι q i V W hi)
    (markedCocartesianFunctorPredicate_reflect_of_markCover q i V W hcover)

/-- 同じ指定辺を覆う単射な同値による制限の core も自明 Kan。 -/
lemma core_markedCocartesianFunctorPre_trivialKanFibration_of_markCover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i.left)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d ∈ W)
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V W hi)) := by
  letI := markedCocartesianFunctorPre_trivialKanFibration_of_markCover q i he V W hi hcover
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
