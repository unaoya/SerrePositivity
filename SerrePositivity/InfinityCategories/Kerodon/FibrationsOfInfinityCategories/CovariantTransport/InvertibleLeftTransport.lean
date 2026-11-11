module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Composition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Identity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberKan

/-!
概要：可逆な底の辺に沿う left fibration の transport は同値。
方針：逆辺の二つの合成三角形と transport の単位・合成同型を使う。
規約：選択済みの実際の標準 transport の同値性。
使われ方：Kerodon §5.2.5（Tag 01VT）、表現の条件の可逆な辺に沿う不変性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：可逆な辺に沿う left fibration の標準 transport は同値。
方針：逆辺の transport を逆射とし、単位と合成の比較を使う。
規約：底 B の quasicategory 性だけを追加する。
使われ方：Kerodon §5.6.8（Tag 02S9）、可逆な分類図式の辺に沿う表現条件の移送。 -/
lemma edgeTransport_isQCatEquivalence_of_isInvertibleEdge {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B.obj (Opposite.op ⦋0⦌)}
    (e : SSet.Edge a b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) := by
  obtain ⟨⟨i, σ, τ⟩⟩ := he.nonempty_inverse
  obtain ⟨hσ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_composition_iso p σ
  obtain ⟨hτ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_composition_iso p τ
  obtain ⟨ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_identity_iso p a
  obtain ⟨hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_identity_iso p b
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p i, ⟨hσ.symm ≪≫ ha⟩, ⟨hτ.symm ≪≫ hb⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
