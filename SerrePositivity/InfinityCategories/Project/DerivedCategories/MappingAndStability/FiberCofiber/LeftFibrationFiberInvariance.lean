module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGFiberTransportSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
/-!
概要：同じ left fibration の fiber 射と相対前合成の同値性を、可逆な底の辺へ沿って移す。
方針：実辺輸送の自然性同型と両輸送の同値を使う。
規約：底も動く同じ正方形を保持する。使われ方：Hom 試験による錐の切断制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma leftFibrationFiberMap_isQCatEquivalence_iff_of_invertibleEdge
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    {a b : B _⦋0⦌} (e : SSet.Edge a b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf a) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isQCatEquivalence_of_isInvertibleEdge p e he
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isQCatEquivalence_of_isInvertibleEdge q e he
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q f hf e
  constructor
  · intro ha
    exact hp.cancel_left ((ha.comp hq).ofFunctorIso hn.symm)
  · intro hb
    exact hq.cancel_right ((hp.comp hb).ofFunctorIso hn)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma leftFibrationSquareFiber_isQCatEquivalence_iff_of_invertibleEdge
    {E B F D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) (q : F ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (e : SSet.Edge a b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h a) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p q f g h b) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isQCatEquivalence_of_isInvertibleEdge p e he
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isQCatEquivalence_of_isInvertibleEdge q (e.map g) (he.map g)
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftFibrationSquareTransportIso p q f g h e
  constructor
  · intro ha
    exact hp.cancel_left ((ha.comp hq).ofFunctorIso hn.symm)
  · intro hb
    exact hq.cancel_right ((hp.comp hb).ofFunctorIso hn)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma relativeFunctorPre_isQCatEquivalence_iff_of_functorIso
    {A D E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : D ⟶ A)
    {a b : A ⟶ B} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i) := by
  have h := leftFibrationSquareFiber_isQCatEquivalence_iff_of_invertibleEdge
    ((ihom A).map p) ((ihom D).map p) ((pre i).app E) ((pre i).app B)
    ((pre i).naturality p).symm (SSet.Edge.ofTruncated e.edge) e.edge_isInvertible
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
