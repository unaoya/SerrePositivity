module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactPartialColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageSmallCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductFromFiniteSubsets
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension

/-!
概要：compact な閉包内射の任意の小さい余積を、compact な部分余極限で回収する。
方針：有限部分余積の左 Kan 図式と濃度変更後の部分余極限を構成する。
規約：元の全余錐と閉包への所属を保持する。
使われ方：実 Ind 像の全小余積閉性への準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- compact な閉包内射の小さい余積を、有限部分余積の同じ全左 Kan 図式で表す。 -/
lemma compactArrowCoproduct_finitePartialDiagram
    (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hbound : IsCardinalChangeBound Cardinal.aleph0 μ)
    {B : Type u}
    (E : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hcompact : ∀ t, Compact.IsKappaCompact.{u, u + 1} μ (E.app _ t))
    (hmem : ∀ t, arrowVertexEdge (E.app _ t) ∈ generatedEdges edges)
    (c : JoinCocone E) (hc : IsColimitCone c) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset B)) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C)
      (d : JoinCocone G), IsColimitCone d ∧ Nonempty (VertexIso d.vertex c.vertex) ∧
      (∀ t, Compact.IsKappaCompact.{u, u + 1} μ (G.app _ t)) ∧
      ∀ t, arrowVertexEdge (G.app _ t) ∈ generatedEdges edges := by
  classical
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  let Y := (ihom (Δ[1] : SSet.{u + 1})).obj C
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := functor_hasSmallColimits Δ[1] hC
  let Z := finiteSubsetFamily B
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget B))
  let δ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Z))
  let F := q ≫ E
  obtain ⟨G, β, hβ⟩ := elementsCoproduct_exists_leftKanExtension Z hY.hasSmallCoproducts F
  obtain ⟨d, hd⟩ := hY (nerve (Finset B)) G
  have hcq : IsColimitCone (c.restrict q) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal q
      (Ind.isRightCofinal_ulift _ (finiteSubsetForget_nerve_isRightCofinal B)) c).mp hc
  have hi := leftKan_colimitVertexIso δ β hβ (c.restrict q) hcq d hd
  have hrow (t : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset B))) _⦋0⦌) :
      Compact.IsKappaCompact.{u, u + 1} μ (G.app _ t) ∧
      arrowVertexEdge (G.app _ t) ∈ generatedEdges edges := by
    rcases t with ⟨t⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective t
    obtain ⟨a, ha, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex s))
    let r := elementsCoproductKanComparison Z s
    have hr := elementsCoproductKanComparison_isRightCofinal Z s
    have har := (Ind.isColimitCone_iff_restrict_rightCofinal r hr a).mp ha
    have : Finite (Z.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    have hsmall : IsKappaSmall μ (nerve (Discrete (Z.obj s))) :=
      isKappaSmall_nerve_of_cardinalChangeBound hbound _
        (hasCardinalLT_of_finite _ _ hbound.1.le)
    have hca : Compact.IsKappaCompact.{u, u + 1} μ (a.restrict r).vertex :=
      isKappaCompact_smallQuasicategoryColimit_universe hbound.1 _ hsmall (a.restrict r) har
        (fun k ↦ hcompact ((r ≫ leftKanProjection δ (ULift.up (nerveVertex s)) ≫ q).app _ k))
    have hsa : arrowVertexEdge (a.restrict r).vertex ∈ generatedEdges edges :=
      (stronglySaturatedClosure_stronglySaturated
        (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1
          (nerve (Discrete (Z.obj s))) _ (a.restrict r) har
          (fun k ↦ hmem ((r ≫ leftKanProjection δ (ULift.up (nerveVertex s)) ≫ q).app _ k))
    rw [JoinCocone.vertex_restrict, hv] at hca hsa
    exact ⟨hca, hsa⟩
  exact ⟨G, d, hd, ⟨by simpa only [JoinCocone.vertex_restrict] using hi⟩,
    fun t ↦ (hrow t).1, fun t ↦ (hrow t).2⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
