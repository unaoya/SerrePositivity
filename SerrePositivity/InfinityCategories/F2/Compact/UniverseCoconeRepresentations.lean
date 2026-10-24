module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseRepresentationRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.JoinQuasicategory
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の一つの全余錐の宇宙変更表現を、図式部分と頂点へ同時に制限する。
方針：元の全余錐の同じ大域表現から両包含で cartesian 制限する。
規約：元の図式・指定頂点・全空間の包含・pointed 写像を厳密に保つ。
使われ方：元の余錐の fiber 写像と、その同じ宇宙変更後の写像の可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} [Quasicategory B] {F : B ⟶ SpaceInfinity.{u}}

/-- 元の全余錐の一つの表現から、同じ元の図式部分への表現を取り出す。 -/
def spaceUniverseCoconeSourceRepresentation (c : JoinCocone F) :
    LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection F)) :=
  spaceUniverseRepresentationRestrict F c.val (joinInl B Δ[0]) c.property

/-- 取り出した図式は、元の図式そのものの指定された宇宙変更。 -/
lemma spaceUniverseCoconeSourceRepresentation_diagram (c : JoinCocone F) :
    (spaceUniverseCoconeSourceRepresentation c).diagram =
      (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u} :=
  spaceUniverseRepresentationRestrict_diagram _ _ _ _

/-- 元の図式の pointed 写像は、全余錐の同じ全空間写像の包含への制限。 -/
lemma spaceUniverseCoconeSourceRepresentation_pointedMap (c : JoinCocone F) :
    (spaceUniverseCoconeSourceRepresentation c).pointedMap =
      (SSet.uliftFunctor.{u + 2, u + 1}).map
        (leftUnstraighteningMap F c.val (joinInl B Δ[0]) c.property) ≫
        (spaceUniverseTransportRepresentation c.val).pointedMap :=
  spaceUniverseRepresentationRestrict_pointedMap _ _ _ _

omit [Quasicategory B] in
/-- 元の右包含への制限は、同じ指定頂点の Yoneda 表示そのもの。 -/
lemma spaceUniverseCocone_vertex_eq (c : JoinCocone F) :
    joinInr B Δ[0] ≫ c.val = SSet.yonedaEquiv.symm c.vertex :=
  (SSet.yonedaEquiv.symm_apply_apply (joinInr B Δ[0] ≫ c.val)).symm

/-- 元の全余錐の同じ表現から、指定頂点そのものへの表現を取り出す。 -/
def spaceUniverseCoconeVertexRepresentation (c : JoinCocone F) :
    LeftTransportRepresentation ((SSet.uliftFunctor.{u + 2, u + 1}).map
      (leftUnstraighteningProjection (SSet.yonedaEquiv.symm c.vertex))) :=
  spaceUniverseRepresentationRestrict (SSet.yonedaEquiv.symm c.vertex) c.val
    (joinInr B Δ[0]) (spaceUniverseCocone_vertex_eq c)

/-- 頂点の図式も、指定した元の頂点そのものの同じ宇宙変更。 -/
lemma spaceUniverseCoconeVertexRepresentation_diagram (c : JoinCocone F) :
    (spaceUniverseCoconeVertexRepresentation c).diagram =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.yonedaEquiv.symm c.vertex) ≫
        spaceUniverseDiagram.{u} :=
  spaceUniverseRepresentationRestrict_diagram _ _ _ _

/-- 指定頂点の pointed 写像も、全余錐の同じ全空間写像の右包含への制限。 -/
lemma spaceUniverseCoconeVertexRepresentation_pointedMap (c : JoinCocone F) :
    (spaceUniverseCoconeVertexRepresentation c).pointedMap =
      (SSet.uliftFunctor.{u + 2, u + 1}).map
        (leftUnstraighteningMap (SSet.yonedaEquiv.symm c.vertex) c.val
          (joinInr B Δ[0]) (spaceUniverseCocone_vertex_eq c)) ≫
        (spaceUniverseTransportRepresentation c.val).pointedMap :=
  spaceUniverseRepresentationRestrict_pointedMap _ _ _ _

end SerrePositivity.InfinityCategories.F2.Compact
