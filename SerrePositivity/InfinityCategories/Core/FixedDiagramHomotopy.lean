module

public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.EquivalenceIntervalVertexIso

/-!
概要：固定図式上の関手圏の同型を相対ホモトピーで表す。
方針：fiber 内の同型を実際の辺で表し、前合成の射影が恒等辺であることを uncurry する。
規約：制限される図式を全時刻で固定する。
使われ方：Kerodon Lemma 4.6.4.25 の固定図式上の自然同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手の辺の前合成が恒等辺なら、ホモトピーは制限する図式上で定値。
方針：前合成と uncurry の自然性を計算する。
規約：区間は第二因子。
使われ方：Kerodon §4.6.4 の相対的な円柱。 -/
lemma simplicialHomotopyOfFunctorEdge_pre_eq_constant {K T X : SSet.{u}}
    {f g : T ⟶ X} (j : K ⟶ T) (p : K ⟶ X)
    (a : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj X))
      (functorVertex f) (functorVertex g))
    (ha : ((pre j).app X).app (Opposite.op ⦋1⦌) a.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X))
        (functorVertex p)).edge) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (simplicialHomotopyOfFunctorEdge a).h =
      fst K Δ[1] ≫ p := by
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm a.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm (((pre j).app X).app (Opposite.op ⦋1⦌) a.edge)) = _
  rw [ha]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, z⟩
  dsimp [SSet.Truncated.Edge.id, functorVertex, uncurry]
  rfl

/-- 概要：固定図式上の関手圏の同型は、図式を全時刻で固定する可逆ホモトピーを与える。
方針：fiber の同型を辺で表し、包含の後で射影が恒等辺となることを使う。
規約：j は単射、X は quasicategory。
使われ方：Kerodon Lemma 4.6.4.25 の join の円柱への入力。 -/
lemma exists_relative_homotopy_of_fixedDiagram_vertexIso
    {K T X : SSet.{u}} [Quasicategory X] (j : K ⟶ T) [Mono j]
    (p : K ⟶ X) (f g : T ⟶ X) (hf : j ≫ f = p) (hg : j ≫ g = p)
    (e : VertexIso (X := vertexFiber ((pre j).app X) (functorVertex p))
      (⟨functorVertex f, by
        change functorVertex (j ≫ f) = PinchedHom.constant (functorVertex p) 0
        rw [hf, pinchedConstant_zero]⟩ : (vertexFiber ((pre j).app X) (functorVertex p)) _⦋0⦌)
      (⟨functorVertex g, by
        change functorVertex (j ≫ g) = PinchedHom.constant (functorVertex p) 0
        rw [hg, pinchedConstant_zero]⟩ : (vertexFiber ((pre j).app X) (functorVertex p)) _⦋0⦌)) :
    ∃ H : SSet.Homotopy f g,
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ p ∧
      ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective _ _ e.hom
  have hai : IsInvertibleEdge (X := vertexFiber ((pre j).app X) (functorVertex p)) a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  let a' := a.map ((truncation 2).map (vertexFiberι ((pre j).app X) (functorVertex p)))
  have hproj : ((pre j).app X).app (Opposite.op ⦋1⦌) a'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (functorVertex p)).edge := by
    change (vertexFiberι ((pre j).app X) (functorVertex p) ≫ (pre j).app X).app
      (Opposite.op ⦋1⦌) a.edge = _
    rw [vertexFiberι_comp]
    rfl
  refine ⟨simplicialHomotopyOfFunctorEdge a',
    simplicialHomotopyOfFunctorEdge_pre_eq_constant j p a' hproj, ?_⟩
  exact simplicialHomotopyOfFunctorEdge_vertex_isInvertible a' (hai.map _)

end SerrePositivity.InfinityCategories
