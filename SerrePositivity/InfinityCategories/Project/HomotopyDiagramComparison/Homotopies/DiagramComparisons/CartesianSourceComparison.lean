module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CartesianPrismComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHomotopyEdges

/-!
概要：同じ終点の Cartesian 輸送の始点側を、底上で可逆な自然な比較により結ぶ。
方針：全頂点で固定した相対延長と Cartesian 辺の消去則を使用する。
規約：指定した元の置換の比較射を変更しない。使われ方：HTT 5.2.4.6 の cf 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 正方形の終点側と両垂直辺が Cartesian なら、始点側も Cartesian。 -/
lemma cartesianSquare_source {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ F)))
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ F)))
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ F))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ F)) := by
  obtain ⟨h00, h01, h10, h11⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.squareTriangle_outerFaces.{u}
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ F) p
    (by simpa only [← Category.assoc, h10] using hx)
    (by simpa only [← Category.assoc, h11] using h₁)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_first_of_second_long (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ F) p
    (by simpa only [← Category.assoc, h01] using hy)
    (by simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle_diagonal] using hd)
  simpa only [← Category.assoc, h00] using h

/-- Cartesian な全垂直辺を持つ prism は、終点側の Cartesian 辺を始点側へ戻す。 -/
lemma cartesianHomotopy_sourceEdge {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (f : (Δ[1] : SSet.{u}) ⟶ A)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H)))
    (hv : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H)) := by
  have hside (j : Fin 2) :
      (lift (𝟙 Δ[1]) (SSet.const (stdSimplex.obj₀Equiv.symm j)) ≫
        (Δ[1] ◁ f)) ≫ H =
      lift (𝟙 Δ[1]) (SSet.const (f.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm j))) ≫ H := by
    rw [lift_whiskerLeft, SSet.const_comp]
  have h := cartesianSquare_source p ((Δ[1] ◁ f) ≫ H)
    (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
      exact h₁)
    (by
      rw [← Category.assoc, hside]
      exact hv (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (by
      rw [← Category.assoc, hside]
      exact hv (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc] at h
  exact h

/-- 元の二つの Cartesian 輸送の始点側を、底の零頂点上の可逆な比較 prism で結ぶ。 -/
lemma cartesianPrism_sourceComparison {A E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ (Δ[1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (H K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH : H ≫ p = fst (Δ[1] : SSet.{u}) A)
    (hK : K ≫ p = fst (Δ[1] : SSet.{u}) A)
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H)
    (hHc : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
    (hKc : ∀ v : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1))) :
    ∃ (α : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
      (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H)
      (h1' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ K),
      α ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ∧
      ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism α h0 h1') v).toTruncated := by
  obtain ⟨J, hJb, hJ1, hJp, hJc⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_cartesianPrismComparison p H K hH hK h1 hKc
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J
  have hαp : α ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianPrismComparison_unit_base p J hJp
  have hb := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianPrismComparison_unit_boundary H K J hJb
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫ ((boundary 1).ι ▷ A)) ≫ α :=
        congrArg (fun k ↦ k ≫ α) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0 A).symm
      _ = _ := by rw [Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  have h1' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ K := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1, Category.assoc, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism α h0 h1'
  refine ⟨α, h0, h1', hαp, ?_⟩
  intro v
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Q v).toTruncated
  have he : e.edge = α.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge α h0 h1' v
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_of_isCartesianEdge p e
  · let f : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ A :=
      lift (𝟙 _) (SSet.const v)
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ J)) := by
      rw [hJ1]
      exact hHc v
    have h := cartesianHomotopy_sourceEdge p J f ht hJc
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (f ≫ α)) at h
    rw [he]
    exact h
  · have hbase := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) hαp
    have hh : (e.map ((truncation 2).map p)).edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).edge := by
      change p.app (Opposite.op ⦋1⦌) e.edge = _
      rw [he]
      exact hbase.trans (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1 = _
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hh).2
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
