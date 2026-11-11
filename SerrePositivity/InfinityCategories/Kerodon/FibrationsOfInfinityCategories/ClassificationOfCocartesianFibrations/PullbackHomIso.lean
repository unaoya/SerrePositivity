module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackHomRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-!
概要：両射影の底変換間の元の cocartesian Hom と、元の標的へ写す局所 Hom は厳密に同型。
方針：全相対関手空間の pullback 同型を、標的の辺の保存・反映で全部分複体へ制限する。
規約：可変の底には quasicategory 性を要求せず、全高次の元の相対作用を保持する。
使われ方：底の余極限の Hom の降下を、実際の各底変換の cocartesian Hom に接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 各底変換の元の全相対 Hom を、元の標的へ写す同じ全相対 Hom と同型化する。 -/
def cocartesianPullbackRawHomIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (a : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.fst a.hom q) (pullback.fst a.hom p) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (pullback.snd a.hom p ≫ p) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso (IsPullback.of_hasPullback a.hom q).flip
    (pullback.fst a.hom p) (pullback.snd a.hom p ≫ p) (by exact pullback.condition)

/-- 同じ全相対 Hom の同型は、元の各底変換の cocartesian 辺の保存条件を反映する。 -/
lemma cocartesianPullbackRawHomIso_predicate {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] (a : Over B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.fst a.hom q) (pullback.fst a.hom p)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom q) v ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
        {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e}
        ((cocartesianPullbackRawHomIso p q a).hom.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨g, hg, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex (pullback.fst a.hom q)
    (pullback.fst a.hom p) v
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges (pullback.fst a.hom p) (pullback.fst a.hom q) g ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q _ _
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso (IsPullback.of_hasPullback a.hom q).flip
        (pullback.fst a.hom p) (pullback.snd a.hom p ≫ p) (by exact pullback.condition)).hom.app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex _ _ g hg))
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate_vertex]
  exact forall_congr' (fun e ↦ imp_congr_right (fun _ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_overPullback_iff q a (g.app (Opposite.op ⦋1⦌) e)))

/-- 元の各底変換の全 cocartesian Hom は、同じ局所 Hom と厳密に同型。 -/
def cocartesianPullbackHomIso {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] (a : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomSpace p q a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (cocartesianPullbackRawHomIso p q a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorPredicate (pullback.fst a.hom p) (pullback.fst a.hom q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
      {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e})
    (cocartesianPullbackRawHomIso_predicate p q a)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
