module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPartialColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageSmallCoproducts
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoproductFromFiniteSubsets
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointKanExtension

/-!
概要：compact な閉包内射の任意の小さい余積を、compact な部分余極限で回収する。
方針：有限部分余積の左 Kan 図式と濃度変更後の部分余極限を構成する。
規約：元の全余錐と閉包への所属を保持する。
使われ方：実 Ind 像の全小余積閉性への準備。

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

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- compact な閉包内射の小さい余積を、有限部分余積の同じ全左 Kan 図式で表す。 -/
lemma compactArrowCoproduct_finitePartialDiagram
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hbound : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound Cardinal.aleph0 μ)
    {B : Type u}
    (E : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hcompact : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (E.app _ t))
    (hmem : ∀ t, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (E.app _ t) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset B)) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C)
      (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex c.vertex) ∧
      (∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ t)) ∧
      ∀ t, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (G.app _ t) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
  classical
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorSmallColimits.functor_hasSmallColimits Δ[1] hC
  let Z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily B
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget B))
  let δ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z))
  let F := q ≫ E
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproduct_exists_leftKanExtension Z hY.hasSmallCoproducts F
  obtain ⟨d, hd⟩ := hY (nerve (Finset B)) G
  have hcq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict q) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget_nerve_isRightCofinal B)) c).mp hc
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKan_colimitVertexIso δ β hβ (c.restrict q) hcq d hd
  have hrow (t : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset B))) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ t) ∧
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (G.app _ t) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
    rcases t with ⟨t⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective t
    obtain ⟨a, ha, hv⟩ := hβ.colimitValue (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))
    let r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Z s
    have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison_isRightCofinal Z s
    have har := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r hr a).mp ha
    have : Finite (Z.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    have hsmall : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve (Discrete (Z.obj s))) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_nerve_of_cardinalChangeBound hbound _
        (hasCardinalLT_of_finite _ _ hbound.1.le)
    have hca : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (a.restrict r).vertex :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hbound.1 _ hsmall (a.restrict r) har
        (fun k ↦ hcompact ((r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) ≫ q).app _ k))
    have hsa : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (a.restrict r).vertex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated
        (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
          (nerve (Discrete (Z.obj s))) _ (a.restrict r) har
          (fun k ↦ hmem ((r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) ≫ q).app _ k))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, hv] at hca hsa
    exact ⟨hca, hsa⟩
  exact ⟨G, d, hd, ⟨by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict] using hi⟩,
    fun t ↦ (hrow t).1, fun t ↦ (hrow t).2⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
