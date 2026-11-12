module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.RelativeFunctor

/-!
概要：始域で指定した辺を cocartesian に送る、元の相対関手の全部分複体。
方針：元の底上の関手の一次成分に指定辺の保存条件を課す。
規約：元の cocartesian 相対 Hom は、その射影の cocartesian 辺を指定した場合に厳密に一致する。
使われ方：余極限の各項で指定辺を保持した Hom 空間の降下。

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

/-- 元の相対関手の頂点が、指定した辺を標的の cocartesian 辺へ送る条件。 -/
def markedCocartesianFunctorPredicate {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a) _⦋0⦌) : Prop :=
  ∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm v).val.app (Opposite.op ⦋1⦌) e)

/-- 実際の底上の関手の頂点では、指定辺を送る元の条件に一致する。 -/
lemma markedCocartesianFunctorPredicate_vertex {A E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (W : Set (A _⦋1⦌)) (f : A ⟶ E) (hf : f ≫ q = a) :
    markedCocartesianFunctorPredicate q a W (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q a f hf) ↔
      ∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) e) := by
  change (∀ e ∈ W, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a) ⟨f, hf⟩)).val.app
      (Opposite.op ⦋1⦌) e)) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 指定辺の保存条件を持つ相対関手の元の全部分複体。 -/
def markedCocartesianFunctorSpace {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q a) (markedCocartesianFunctorPredicate q a W)

/-- 元の標的が inner fibration なら、指定辺を保つ相対関手の空間は quasicategory。 -/
instance markedCocartesianFunctorSpace_quasicategory {A E B : SSet.{u}}
    (q : E ⟶ B) [InnerFibration q] (a : A ⟶ B) (W : Set (A _⦋1⦌)) :
    Quasicategory (markedCocartesianFunctorSpace q a W) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- cocartesian 辺そのものを指定すると、元の全 cocartesian 相対 Hom を厳密に回収する。 -/
lemma markedCocartesianFunctorSpace_cocartesian {A E B : SSet.{u}} (p : A ⟶ B) (q : E ⟶ B) :
    markedCocartesianFunctorSpace q p {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
