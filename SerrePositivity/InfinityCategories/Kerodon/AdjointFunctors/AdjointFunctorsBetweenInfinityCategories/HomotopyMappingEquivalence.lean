module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CartesianIntervalPostcomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyPrism

/-!
概要：指定輸送の評価成分の前後合成に、元の Cartesian・coCartesian 辺の同値性を移す。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較と一般 coherent 極限保存は別工程。使われ方：HTT 5.2.4.6。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
noncomputable section

/-- 一次単体で指定した元の Cartesian 辺の後合成は、下段始域の写像空間上で同値。 -/
lemma intervalPostcompose_isSimplicialHomotopyEquivalence_of_cartesianEdge
    {E : SSet.{u}} [Quasicategory E] {a b : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) a b) (x : E _⦋0⦌)
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (hp : p.app (Opposite.op ⦋1⦌) f.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p f.edge)
    (hx : p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose x
      (SSet.Truncated.HomotopyCategory.homMk f)) := by
  let q : E.op ⟶ (Δ[1] : SSet.{u}) :=
    SSet.opFunctor.map p ≫ (stdSimplex.opIso ⦋1⦌).hom
  have hq : q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := E) f).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    change (stdSimplex.opIso ⦋1⦌).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (p.app (Opposite.op ⦋1⦌) f.edge)) = _
    rw [hp]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hfc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := E) f).edge :=
    hf.op.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration (stdSimplex.opIso ⦋1⦌).hom _)
  have hqx : q.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    change (stdSimplex.opIso ⦋1⦌).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (p.app (Opposite.op ⦋0⦌) x)) = _
    rw [hx]
    rfl
  have hpre := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesianEdge
    (E := E.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := E) f) (SSet.opObjEquiv.symm x) q hq hfc hqx
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPostcompose_isSimplicialHomotopyEquivalence_of_op_precompose (E := E) x f hpre

/-- 標準区間上の指定ホモトピーの各点の辺は、元の標準辺を被覆する。 -/
lemma homotopyVertexEdge_projection {A E : SSet.{u}} {U V : A ⟶ E}
    (H : SSet.Homotopy U V) (p : E ⟶ (Δ[1] : SSet.{u}))
    (hp : H.h ≫ p = snd A (Δ[1] : SSet.{u})) (x : A _⦋0⦌) :
    p.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
  exact congrArg (fun q : A ⊗ (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ↦
    q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hp

/-- 指定 coCartesian 輸送の評価成分による前合成は、上段終域への写像空間上で同値。 -/
lemma intervalPrecompose_equivalence_of_cocartesianHomotopy
    {A E : SSet.{u}} [Quasicategory E] {U V : A ⟶ E}
    (H : SSet.Homotopy U V) (p : E ⟶ (Δ[1] : SSet.{u}))
    (hp : H.h ≫ p = snd A (Δ[1] : SSet.{u}))
    (hc : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge)
    (x : A _⦋0⦌) (y : E _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesianEdge
    (E := E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated y p
    (homotopyVertexEdge_projection H p hp x) (hc x) hy

/-- 指定 Cartesian 輸送の評価成分による後合成は、下段始域の写像空間上で同値。 -/
lemma intervalPostcompose_equivalence_of_cartesianHomotopy
    {A E : SSet.{u}} [Quasicategory E] {U V : A ⟶ E}
    (H : SSet.Homotopy U V) (p : E ⟶ (Δ[1] : SSet.{u}))
    (hp : H.h ≫ p = snd A (Δ[1] : SSet.{u}))
    (hc : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge)
    (x : A _⦋0⦌) (y : E _⦋0⦌)
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose y
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  exact intervalPostcompose_isSimplicialHomotopyEquivalence_of_cartesianEdge
    (E := E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated y p
    (homotopyVertexEdge_projection H p hp x) (hc x) hy

end
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
