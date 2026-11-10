module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.FiniteDiscreteShapes
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductFromFiniteSubsets
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationPreservation

/-!
概要：固定始域の閉包内射圏の全小余積と、包含による指定余錐の保存。
方針：元の有限部分余積を全左 Kan 図式でまとめ、filtered な有限部分集合上で余極限を取る。
規約：空添字を含み、元の全余錐の頂点を同型不変性で回収する。
使われ方：HTT 5.5.5.11 の全小余極限への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域の閉包内射の任意の小余積は、元の全 coslice でも閉包内に留まる。 -/
lemma generatedSource_coproduct_colimit_mem (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) {B : Type u}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶ generatedSourceCategory edges x)
    (c : JoinCocone (D ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  classical
  let Y := sliceUnder (SSet.yonedaEquiv.symm x)
  let U := generatedSourceInclusion edges x
  let E := D ≫ U
  have hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y := sourceCoslice_hasSmallColimits hC x
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
  let P := fun c : Y _⦋0⦌ ↦ (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges
  have hG : ∀ t, P (G.app _ t) := by
    rintro ⟨t⟩
    obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective t
    obtain ⟨a, ha, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex s))
    let r := elementsCoproductKanComparison Z s
    have hr := elementsCoproductKanComparison_isRightCofinal Z s
    have har := (Ind.isColimitCone_iff_restrict_rightCofinal r hr a).mp ha
    have : Finite (Z.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    have := uliftDiscreteNerve_finite.{u, u + 1} (Z.obj s)
    let Drow := r ≫ leftKanProjection δ (ULift.up (nerveVertex s)) ≫ q ≫ D
    let ar : JoinCocone (Drow ≫ U) := ⟨(a.restrict r).val, by
      simpa only [Drow, F, E, δ, leftKanDiagram, Category.assoc] using (a.restrict r).property⟩
    have har' : IsColimitCone ar :=
      (isColimitCone_iff_of_cocone_val_eq (a.restrict r) ar rfl).mp har
    have hm := generatedSource_finite_colimit_mem hC edges x _ Drow ar har'
    change P (a.restrict r).vertex at hm
    rw [JoinCocone.vertex_restrict, hv] at hm
    exact hm
  let G' := fullSubcomplexLift P G hG
  let d' : JoinCocone (G' ≫ U) := ⟨d.val, by
    rw [d.property]
    exact (fullSubcomplexLift_ι P G hG).symm⟩
  have hd' : IsColimitCone d' := (isColimitCone_iff_of_cocone_val_eq d d' rfl).mp hd
  have hm := generatedSource_nerve_colimit_mem edges x (Finset B)
    (isWeaklyContractible_of_isFilteredInfinity _) G' d' hd'
  change P d.vertex at hm
  exact (generatedSourceCondition_iff_vertexIso edges x
    (show VertexIso d.vertex c.vertex from by
      simpa only [JoinCocone.vertex_restrict] using hi)).mp hm

/-- 同じ周囲の全余錐から、包含に保存される元の小余積を内部に構成する。 -/
lemma generatedSource_hasPreservedCoproduct (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) (B : Type u)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⟶
      generatedSourceCategory edges x) :
    Ind.HasPreservedColimit (generatedSourceInclusion edges x) D := by
  obtain ⟨c, hc⟩ := (sourceCoslice_hasSmallColimits hC x).hasSmallCoproducts B
    (D ≫ generatedSourceInclusion edges x)
  let P := fun c : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌ ↦
    (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges
  have hm : P c.vertex := generatedSource_coproduct_colimit_mem hC edges x D c hc
  refine ⟨Ind.fullCoconeLift P D c hm, Ind.fullCoconeLift_isColimit P D c hm hc, ?_⟩
  have hi : mapJoinCocone (generatedSourceInclusion edges x) (Ind.fullCoconeLift P D c hm) = c :=
    Ind.fullCoconeLift_inclusion P D c hm
  exact hi.symm ▸ hc

/-- 固定始域の閉包内射圏は全小余積を持つ。 -/
lemma generatedSource_hasSmallCoproducts (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : HasSmallCoproducts (generatedSourceCategory edges x) := by
  intro B D
  obtain ⟨c, hc, _⟩ := generatedSource_hasPreservedCoproduct hC edges x B D
  exact ⟨c, hc⟩

/-- 元の全 coslice への包含は、任意の指定小余積余錐を保存する。 -/
lemma generatedSourceInclusion_preservesSmallCoproducts (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    PreservesSmallCoproducts (generatedSourceInclusion edges x) := by
  intro B D c hc
  exact (generatedSource_hasPreservedCoproduct hC edges x B D).map_isColimit c hc

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
