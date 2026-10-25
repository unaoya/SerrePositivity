module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceCoproducts
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceFiniteColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.FiniteCoproductColimitGeneration

/-!
概要：固定始域の閉包内射圏の小余完備性と、包含による全小余極限の保存を構成する。
方針：公開 P-11 に構成済みの小余積と全有限余極限を渡す。
規約：accessibility・presentable 性・終対象の存在はまだ主張しない。
使われ方：HTT 5.5.5.11・14 の固定始域圏の存在部分。
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
  (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
include hC

/-- 固定始域圏の任意の小図式には、周囲で保存される同じ普遍余錐がある。 -/
lemma generatedSource_hasPreservedSmallColimit
    (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedSourceCategory edges x) :
    Ind.HasPreservedColimit (generatedSourceInclusion edges x) D :=
  hasPreservedColimit_of_coproducts_finite (generatedSourceInclusion edges x)
    (generatedSource_hasSmallCoproducts hC edges x)
    (generatedSourceInclusion_preservesSmallCoproducts hC edges x)
    (generatedSource_hasPreservedFiniteColimit hC edges x) K D

/-- 固定始域圏は全ての小余極限を持つ。 -/
lemma generatedSource_hasSmallColimits : HasSmallColimits (generatedSourceCategory edges x) := by
  intro K D
  obtain ⟨c, hc, _⟩ := generatedSource_hasPreservedSmallColimit hC edges x K D
  exact ⟨c, hc⟩

/-- 全 coslice 圏への包含は元の指定小余極限余錐を保つ。 -/
lemma generatedSourceInclusion_preservesSmallColimits :
    PreservesSmallColimits (generatedSourceInclusion edges x) := by
  intro K D c hc
  exact (generatedSource_hasPreservedSmallColimit hC edges x K D).map_isColimit c hc

/-- 閉包内の任意の小図式の周囲での指定余極限も、同じ閉包条件を満たす。 -/
lemma generatedSource_small_colimit_mem
    (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedSourceCategory edges x)
    (c : JoinCocone (D ≫ generatedSourceInclusion edges x)) (hc : IsColimitCone c) :
    (JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  obtain ⟨d, hd, hUd⟩ := generatedSource_hasPreservedSmallColimit hC edges x K D
  have hm : (JoinCocone.leg
      (mapJoinCocone (generatedSourceInclusion edges x) d).vertex (𝟙 Δ[0])).edge ∈
        generatedEdges edges := by
    rw [Ind.mapJoinCocone_vertex]
    exact fullSubcomplexOnVertices_vertex d.vertex
  have hi := VertexIso.map
    (colimitConeIso (mapJoinCocone (generatedSourceInclusion edges x) d) c hUd hc)
    (sliceUnderProjection (D ≫ generatedSourceInclusion edges x))
  exact (generatedSourceCondition_iff_vertexIso edges x hi).mp hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
