module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Ho
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：端点を明示した辺に沿う transport。
方針：辺に添えられた始点と終点の等式で既存の transport を添字付け直す。
規約：fiber の添字を零単体の式でなく指定された端点に固定する。
使われ方：Kerodon Example 5.2.2.5（Tag 019P）、Proposition 5.2.5.1（Tag 01VU） の恒等と合成の記述。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：指定した端点を持つ辺に沿う cocartesian な transport の性質。
方針：端点の fiber と底の辺を固定した cocartesian な prism を要求する。
規約：辺は二切断の端点付き辺として表す。
使われ方：Kerodon Definition 5.2.2.4（Tag 019N）、恒等と合成の比較。 -/
@[kerodon 019N]
def IsEdgeTransport {X B : SSet.{u}} (p : X ⟶ B) {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) : Prop :=
  ∃ H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ X,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ∧
    H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge ∧
    ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1))

/-- 概要：端点を指定した辺に沿う transport 関手を一つ選ぶ。
方針：端点の等式で既存の選択された transport に帰着する。
規約：値域と定義域の fiber の添字は入力された端点。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、Proposition 5.2.5.1（Tag 01VU） の合成則。 -/
@[kerodon 023Y]
noncomputable def edgeTransport {X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b := by
  rcases e with ⟨s, hs, ht⟩
  subst a
  subst b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianTransport p s

/-- 概要：端点を指定して選択した transport は cocartesian な証人を持つ。
方針：端点の等式を消去して既存の証人を使う。
規約：新たな持ち上げの選択を行わない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、edgeTransport の正当性。 -/
lemma edgeTransport_isTransport {X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    IsEdgeTransport p e (edgeTransport p e) := by
  rcases e with ⟨s, hs, ht⟩
  subst a
  subst b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianTransport_isTransport p s

/-- 概要：同じ端点付き辺に沿う二つの transport は終点 fiber 内で同型。
方針：端点の等式を消去して一般の証人比較を使う。
規約：同型は FunctorIso である。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、恒等・合成の比較の利用側 API。 -/
lemma IsEdgeTransport.functorIso {X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b}
    (hF : IsEdgeTransport p e F) (hG : IsEdgeTransport p e G) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) := by
  rcases e with ⟨s, hs, ht⟩
  subst a
  subst b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianTransport.functorIso p s hF hG

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
