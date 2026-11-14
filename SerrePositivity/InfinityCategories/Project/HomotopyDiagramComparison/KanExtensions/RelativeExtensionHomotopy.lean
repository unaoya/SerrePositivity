module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramHomotopy

/-!
概要：底と初期部分図式を同時に固定した、二つの相対延長の実際のホモトピー。
方針：相対関手の自明な制限の fiber 内で辺を選び、内部 Hom の辺を uncurry する。
規約：単なる終点の同型を選ばず、ホモトピー自体の底と初期制限の式を保持する。
使われ方：元の三角形 prism の長辺と標準輸送 prism の、二単体への依存を保つ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ底と同じ left anodyne な初期値を持つ二つの延長は、その両方を保つホモトピーで結べる。 -/
lemma exists_homotopy_over_fixed_extension {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (β : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W W' : A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v) :
    ∃ H : SSet.Homotopy W W',
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ β ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_trivialKanFibration p β i hi
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p β W hW
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p β W' hW'
  have hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv := by
    simpa only [hWi] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex p β i W hW
  have hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i).app (Opposite.op ⦋0⦌) y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv := by
    simpa only [hWi'] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex p β i W' hW'
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_edge_over_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i) x y
    (hx.trans hy.symm)
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β)
  let a := k.map ((truncation 2).map ι)
  have hbase : ((ihom A).map p).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj B))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β)).edge := by
    change (ι ≫ (ihom A).map p).app (Opposite.op ⦋1⦌) k.edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex β) 1 = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  have hpre : ((pre i).app E).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom D).obj E))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)).edge := by
    let ι' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ β))
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β ⟶ (ihom D).obj E ↦
      s.app (Opposite.op ⦋1⦌) k.edge) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι p β i)
    change ι'.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i).app (Opposite.op ⦋1⦌) k.edge) =
        ((pre i).app E).app (Opposite.op ⦋1⦌) a.edge at hh
    rw [hk, hy] at hh
    have hid := congrArg SSet.Truncated.Edge.edge
      (SSet.Truncated.Edge.map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv)
        ((truncation 2).map ι'))
    exact hh.symm.trans hid
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p β a hbase,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyOfFunctorEdge_pre_eq_constant i v a hpre⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
