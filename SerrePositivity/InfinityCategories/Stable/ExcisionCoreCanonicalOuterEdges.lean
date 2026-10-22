module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreInputComposite
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

lemma excisionCoreSourceOuterCone_eq {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCorePuncturedOuterCone (excisionCorePuncturedSourceCone F) =
      pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1) :=
  Subtype.ext (excisionCorePuncturedSourceCone_outer_val F)

def excisionCoreSourceToCanonicalOuterConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) e := by
  have h := excisionCoreSourceToOuterConeEdge F e he
  simpa only [excisionCoreSourceOuterCone_eq] using h

lemma excisionCoreSourceToCanonicalOuterConeEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    (excisionCoreSourceToCanonicalOuterConeEdge F e he).edge =
      (excisionCoreSourceToOuterConeEdge F e he).edge := by
  dsimp only [excisionCoreSourceToCanonicalOuterConeEdge]
  apply truncatedEdge_cast_edge
  · exact excisionCoreSourceOuterCone_eq F
  · rfl

lemma excisionCoreSourceToCanonicalOuterConeEdge_projected_edge {X : SSet.{u}}
    [Quasicategory X] (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    let q := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
    ((excisionCoreSourceToCanonicalOuterConeEdge F e he).map ((truncation 2).map q)).edge =
      ((excisionCoreSourceToOuterConeEdge F e he).map ((truncation 2).map q)).edge := by
  intro q
  rw [Truncated.Edge.map_edge, excisionCoreSourceToCanonicalOuterConeEdge_edge]
  rfl

end SerrePositivity.InfinityCategories
