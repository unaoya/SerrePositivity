module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramUniversalTransport

/-!
概要：空間の射の同値性を普遍 pointed-space 射影の transport で検出する。
方針：一つの射を二対象の strict な Kan 値図式として扱い、係数の射の判定を適用する。
規約：端点の表示が異なる辺も、一単体が同じなら同じ同値性の判定を持つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍 left fibration の作用の同値性の反映。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：一単体が等しい辺の標準 transport は同じ同値性の判定を持つ。
方針：一単体の面から両端点の等式を取り出し、辺の等式に帰着する。
規約：端点を等号で変更した辺の表示を許す。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、Corollary 5.6.0.6（Tag 028T）、coherent な辺の表示の変更。 -/
lemma edgeTransport_isQCatEquivalence_congr_edge {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b a' b' : B _⦋0⦌}
    (e : SSet.Edge a b) (e' : SSet.Edge a' b') (h : e.edge = e'.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e') := by
  have ha : a = a' := e.src_eq.symm.trans
    ((congrArg (fun z ↦ B.δ 1 z) h).trans e'.src_eq)
  have hb : b = b' := e.tgt_eq.symm.trans
    ((congrArg (fun z ↦ B.δ 0 z) h).trans e'.tgt_eq)
  subst a'
  subst b'
  have he : e = e' := SSet.Edge.ext h
  subst e'
  rfl

/-- 概要：Kan 複体の射に沿う普遍射影の transport が同値であることと、その射が同値であることは同値。
方針：持ち上げた二点順序上の図式に射を組み込み、図式の辺の coherent 表示を計算する。
規約：任意の Kan 複体間の射を扱い、射の可逆性は仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、𝒮 の辺に対する普遍射影の作用の同値性の検出。 -/
lemma pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff
    {K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (f : K ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  let D : ULift.{u} (Fin 2) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
      ComposableArrows.mk₁ f
  let g : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ⟶ ULift.up 1 := homOfLE (by decide)
  have hg : D.map g = f := rfl
  let e := SSet.Edge.map
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve D)
  have he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge D g).trans
      (congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge z).edge) hg)
  exact (edgeTransport_isQCatEquivalence_congr_edge _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) he).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramUniversalTransport_isQCatEquivalence_iff D g)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
