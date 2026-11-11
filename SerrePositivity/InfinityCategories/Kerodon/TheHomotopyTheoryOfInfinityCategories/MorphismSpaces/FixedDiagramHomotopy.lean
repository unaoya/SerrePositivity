module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceIntervalVertexIso

/-!
概要：固定図式上の関手圏の同型を相対ホモトピーで表す。
方針：fiber 内の同型を実際の辺で表し、前合成の射影が恒等辺であることを uncurry する。
規約：制限される図式を全時刻で固定する。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の固定図式上の自然同型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：関手の辺の前合成が恒等辺なら、ホモトピーは制限する図式上で定値。
方針：前合成と uncurry の自然性を計算する。
規約：区間は第二因子。
使われ方：Kerodon §4.6.4（Tag 01KE） の相対的な円柱。 -/
lemma simplicialHomotopyOfFunctorEdge_pre_eq_constant {K T X : SSet.{u}}
    {f g : T ⟶ X} (j : K ⟶ T) (p : K ⟶ X)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    (ha : ((pre j).app X).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).edge) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a).h =
      fst K Δ[1] ≫ p := by
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm a.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm (((pre j).app X).app (Opposite.op ⦋1⦌) a.edge)) = _
  rw [ha]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, z⟩
  dsimp [SSet.Truncated.Edge.id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex, uncurry]
  rfl

/-- 概要：固定図式上の関手圏の同型は、図式を全時刻で固定する可逆ホモトピーを与える。
方針：fiber の同型を辺で表し、包含の後で射影が恒等辺となることを使う。
規約：j は単射、X は quasicategory。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の join の円柱への入力。 -/
lemma exists_relative_homotopy_of_fixedDiagram_vertexIso
    {K T X : SSet.{u}} [Quasicategory X] (j : K ⟶ T) [Mono j]
    (p : K ⟶ X) (f g : T ⟶ X) (hf : j ≫ f = p) (hg : j ≫ g = p)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0
        rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌)
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ g) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0
        rw [hg, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌)) :
    ∃ H : SSet.Homotopy f g,
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p ∧
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e.hom
  have hai : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  let a' := a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)))
  have hproj : ((pre j).app X).app (Opposite.op ⦋1⦌) a'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫ (pre j).app X).app
      (Opposite.op ⦋1⦌) a.edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
    rfl
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a',
    simplicialHomotopyOfFunctorEdge_pre_eq_constant j p a' hproj, ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible a' (hai.map _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
