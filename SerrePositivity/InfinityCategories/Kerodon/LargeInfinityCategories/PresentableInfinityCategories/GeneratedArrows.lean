module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Generators
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.StronglySaturatedClosure
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullCoconeLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContractibleConstantColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence

/-!
概要：小さい辺族の強飽和生成閉包を、元の全射圏の全部分圏として構成する。
方針：閉包の余極限閉性から、周囲の同じ全余錐を全部分圏へ持ち上げる。
規約：accessibility・presentable 性・局所置換の存在はここでは主張しない。
使われ方：P-1 f2、HTT 5.5.4.14 の飽和射圏の余完備性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の小さい生成族が生成する強飽和な辺集合。 -/
def generatedEdges (edges : I → C _⦋1⦌) : Set (C _⦋1⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)

/-- 強飽和生成閉包に属する元の射を全高次単体と共に保持する全部分圏。 -/
def generatedArrowCategory (edges : I → C _⦋1⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u + 1})).obj C)
    (fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ generatedEdges edges)

instance generatedArrowCategory_quasicategory (edges : I → C _⦋1⦌) :
    Quasicategory (generatedArrowCategory edges) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 元の全射圏への全部分包含。 -/
def generatedArrowInclusion (edges : I → C _⦋1⦌) :
    generatedArrowCategory edges ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ generatedEdges edges)).ι

/-- 元の射圏への包含は充満忠実。 -/
lemma generatedArrowInclusion_isFullyFaithful (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (generatedArrowInclusion edges) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 小生成性の添字は、最初に指定した小さい辺族そのもの。 -/
lemma generatedEdges_smallGeneration (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsOfSmallStrongGeneration (SSet.uliftFunctor.{u + 1, u}).obj (generatedEdges edges) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_range_smallGeneration _ edges

/-- 射圏内で同型な二頂点は、元の生成閉包への所属が一致する。 -/
lemma generatedArrow_mem_iff_vertexIso (edges : I → C _⦋1⦌)
    {f g : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso f g) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ generatedEdges edges ↔ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge g ∈ generatedEdges edges := by
  suffices h : ∀ {f g : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌},
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso f g → _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ generatedEdges edges →
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge g ∈ generatedEdges edges from ⟨h e, h e.symm⟩
  intro f g e hf
  let K := (SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u})
  have hK : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (stdSimplex.isTerminalObj₀.from K) := by
    have he : stdSimplex.isTerminalObj₀.from K = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0).hom :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso _
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone K f
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone_isColimit_of_pointCofinal hK f
  have hv : c.vertex = f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
    change SSet.yonedaEquiv (_ ≫ SSet.const f) = f
    rw [SSet.comp_const, ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]
  obtain ⟨d, hd, hvd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hv) ≪≫ e)
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
      (Δ[0] : SSet.{u}) (SSet.const f) d hd (fun _ ↦ by
        simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id, Functor.map_id_apply]
        exact hf)
  rwa [hvd] at hm

/-- 飽和射圏の図式の周囲の任意小余極限は、同じ生成閉包に属する。 -/
lemma generatedArrow_colimit_mem (edges : I → C _⦋1⦌)
    {K : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedArrowCategory edges)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ generatedArrowInclusion edges)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge c.vertex ∈ generatedEdges edges := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1 K
      (D ≫ generatedArrowInclusion edges) c hc
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (D.app _ k)

/-- 元の飽和射圏は小余極限を持つ。accessibility は別に構成する。 -/
lemma generatedArrow_hasSmallColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (generatedArrowCategory edges) := by
  intro K D
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC K
    (D ≫ generatedArrowInclusion edges)
  let P := fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ generatedEdges edges
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoconeLift P D c (generatedArrow_colimit_mem edges D c hc)
  exact ⟨d, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoconeLift_isColimit P D c
    (generatedArrow_colimit_mem edges D c hc) hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
