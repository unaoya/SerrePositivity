module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCanonicalOuterEdges
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

lemma excisionCoreInput_to_outer_vertex {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)).vertex =
      (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)).vertex :=
  (excisionCoreSourceOuter_to_input_vertex F).symm.trans
    (congrArg JoinCone.vertex (excisionCoreSourceOuterCone_eq F))

lemma excisionCoreComparisonEdge_canonical_composite {X : SSet.{u}} [Quasicategory X]
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
            (excisionCoreInput_to_outer_vertex F)) ≫
              Truncated.HomotopyCategory.homMk
                ((excisionCoreSourceToCanonicalOuterConeEdge F e he).map
                  ((truncation 2).map qo)) := by
  intro qi qo
  have h := excisionCoreComparisonEdge_input_composite F d hd e he
  dsimp only at h
  have ht := homMk_edge_square_of_edge_eq
    ((excisionCoreSourceToOuterConeEdge F e he).map ((truncation 2).map qo))
    ((excisionCoreSourceToCanonicalOuterConeEdge F e he).map ((truncation 2).map qo))
    (congrArg JoinCone.vertex (excisionCoreSourceOuterCone_eq F)) rfl
    (excisionCoreSourceToCanonicalOuterConeEdge_projected_edge F e he).symm
  simp only [eqToHom_refl, Category.comp_id] at ht
  rw [ht, ← Category.assoc, eqToHom_trans] at h
  exact h

lemma excisionCoreComparisonEdge_canonical_composite_of_edges {X : SSet.{u}}
    [Quasicategory X] (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e)
    (a : Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) d)
    (b : Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) e) :
    let qi := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))
    let qo := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
    Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map qi)) ≫
      Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he) =
        eqToHom (congrArg (fun v ↦ (HomotopyCategory.mk v : hoFunctor.obj X))
          (excisionCoreInput_to_outer_vertex F)) ≫
            Truncated.HomotopyCategory.homMk (b.map ((truncation 2).map qo)) := by
  intro qi qo
  have ha := congrArg ((Truncated.mapHomotopyCategory ((truncation 2).map qi)).map)
    (excisionCoreSourceToInputConeEdge_hom_eq F d hd a)
  have hb : Truncated.HomotopyCategory.homMk
      (excisionCoreSourceToCanonicalOuterConeEdge F e he) =
        Truncated.HomotopyCategory.homMk b := he.isTerminalHo.hom_ext _ _
  have hbp := congrArg ((Truncated.mapHomotopyCategory ((truncation 2).map qo)).map) hb
  simp only [Truncated.mapHomotopyCategory_homMk] at ha hbp
  have h := excisionCoreComparisonEdge_canonical_composite F d hd e he
  dsimp only at h
  rw [ha, hbp] at h
  exact h

end SerrePositivity.InfinityCategories
