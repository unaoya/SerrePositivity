module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.OrdinaryCoherentNatTransPrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：区間上の指定端点の fiber へ関手自然同型を反映する。
方針：底の薄さで prism を fiber に持ち上げ、全忠実性で成分の可逆性を反映する。
規約：指定 fiber 同型と元の包含を保持。使われ方：元の左導来関手との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 両端の底が同じ区間頂点なら、prism 全体の底はその定値写像。 -/
lemma prism_base_constant_of_endpoints {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (b : Fin 2)
    (h0 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm b))
    (h1 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm b)) :
    H ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm b) := by
  apply (cancel_mono (stdSimplex.isoNerve 1).hom).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨t, x⟩
  obtain ⟨j, rfl⟩ := (stdSimplex.obj₀Equiv (n := 1)).symm.surjective t
  fin_cases j
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) h0
    change p.app (Opposite.op ⦋0⦌)
      (H.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 0, x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm b) 0 at h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
    exact congrArg (fun y ↦ (stdSimplex.isoNerve 1).hom.app (Opposite.op ⦋0⦌) y) h
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) h1
    change p.app (Opposite.op ⦋0⦌)
      (H.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 0, x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm b) 0 at h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
    exact congrArg (fun y ↦ (stdSimplex.isoNerve 1).hom.app (Opposite.op ⦋0⦌) y) h

/-- 全空間の関手自然同型を、指定端点の全忠実な fiber へ反映する。 -/
lemma endpointFunctorIso_reflection {A E X : SSet.{u}} [Quasicategory E] [Quasicategory X]
    (p : E ⟶ (Δ[1] : SSet.{u})) (b : Fin 2)
    (i : X ⟶ E) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i)
    (e : X ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm b))
    (he : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm b) = i)
    {f g : A ⟶ X} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ i) (g ≫ i)) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) := by
  have him : Mono i := by rw [← he]; infer_instance
  have hip : i ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm b) := by
    rw [← he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  let H := h.simplicialHomotopy
  let P := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have hP0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P = f ≫ i := by
    change SSet.ι₀ ≫ H.h = _
    exact H.h₀
  have hP1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P = g ≫ i := by
    change SSet.ι₁ ≫ H.h = _
    exact H.h₁
  have hp : P ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm b) := by
    apply prism_base_constant_of_endpoints p P b
    · rw [hP0, Category.assoc, hip, SSet.comp_const]
    · rw [hP1, Category.assoc, hip, SSet.comp_const]
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (stdSimplex.obj₀Equiv.symm b) P hp ≫ e.inv
  have hQi : Q ≫ i = P := by
    dsimp only [Q]
    rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hQ0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ Q = f := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hQi, hP0]
  have hQ1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ Q = g := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hQi, hP1]
  have hPH : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism P hP0 hP1 = H := by
    apply SSet.RelativeMorphism.Homotopy.ext
    rfl
  have hiH (x : A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
    have hi := h.edge_isInvertible.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge h.edge x)).mpr hi
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism Q hQ0 hQ1) ?_⟩
  intro x
  apply hf.reflects_isInvertibleEdge
  have hed : ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism Q hQ0 hQ1) x).toTruncated.map
      ((truncation 2).map i)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism P hP0 hP1) x).edge := by
    change i.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism Q hQ0 hQ1) x).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge]
    exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) hQi
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hed).2
  rw [hPH]
  exact hiH x

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
