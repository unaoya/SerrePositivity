module
public import SerrePositivity.InfinityCategories.Stable.EdgeHomotopyTransportSquare
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceLimitEdges
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonFirstComposite

/-!
概要：実 θ の第一合成式を、元の内外の pullback 錐の比較辺へ同定する。
方針：正規化した入力制限と同じ頂点射影、極限錐への辺の一意性を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionCoreSourceOuter_to_input_vertex {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (excisionCorePuncturedOuterCone (excisionCorePuncturedSourceCone F)).vertex =
      (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)).vertex := by
  rw [excisionCorePuncturedOuterCone_vertex]
  have h := congrArg JoinCone.vertex (excisionCoreInputConeRestriction_source F)
  rw [excisionCoreInputConeRestriction_cone, JoinCone.vertex_cast,
    restrictJoinCone_vertex] at h
  exact h

lemma excisionCoreComparisonEdge_input_composite {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    let qi := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))
    let qo := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
    Truncated.HomotopyCategory.homMk
      ((excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map qi)) ≫
        Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he) =
          eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X))
            (excisionCoreSourceOuter_to_input_vertex F).symm) ≫
              Truncated.HomotopyCategory.homMk
                ((excisionCoreSourceToOuterConeEdge F e he).map ((truncation 2).map qo)) := by
  intro qi qo
  have h := excisionCoreComparisonEdge_first_composite F d hd e he
  have ht := homMk_edge_square_of_edge_eq
    ((excisionCoreSourceToLimitOuterConeEdge F d hd).map ((truncation 2).map qo))
    ((excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map qi))
    (excisionCoreSourceOuter_to_input_vertex F)
    ((excisionCorePuncturedOuterCone_vertex _).trans
      (excisionCorePuncturedLimitCone_vertex F d hd))
    ((excisionCoreSourceToLimitOuterConeEdge_projected_edge F d hd).trans
      (excisionCoreSourceToInputConeEdge_projected_edge F d hd).symm)
  dsimp only at h
  rw [← Category.assoc, ht] at h
  apply (cancel_epi (eqToHom (congrArg
    (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X))
      (excisionCoreSourceOuter_to_input_vertex F)))).mp
  simpa only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using h

end SerrePositivity.InfinityCategories
