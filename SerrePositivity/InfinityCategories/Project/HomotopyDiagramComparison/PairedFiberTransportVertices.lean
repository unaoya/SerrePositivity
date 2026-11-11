module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.TensorHomotopyEquivalence

/-!
概要：二つの fiber 輸送の対の同値性は、三つの端点の表示によらない。
方針：端点の等号を消去し、同じ raw 辺を持つ端点付き辺を同定する。
規約：同値性を弱めず、元の同じ輸送射について述べる。
使われ方：積関手の頂点表示から元の Kan 直積の頂点表示への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 三つの端点の表示だけを変えても、二つの元の輸送の対の同値性は変わらない。 -/
lemma pairedFiberTransport_isQCatEquivalence_iff_of_vertices
    {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {a b c a' b' c' : B _⦋0⦌} (ha : a = a') (hb : b = b') (hc : c = c')
    (e : SSet.Edge a b) (f : SSet.Edge a c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.ofEq ha hb))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (f.ofEq ha hc))) := by
  subst a'
  subst b'
  subst c'
  have he : e.ofEq rfl rfl = e := by
    apply SSet.Edge.ext
    rfl
  have hf : f.ofEq rfl rfl = f := by
    apply SSet.Edge.ext
    rfl
  rw [he, hf]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
