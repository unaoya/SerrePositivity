module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationCartesianRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UniverseKanPullback

/-!
概要：元の大域的な宇宙変更表現を、元の図式制限の全空間へ同時に制限する。
方針：実際の unstraightening の引き戻し正方形を持ち上げ、cartesian 制限を使う。
規約：分類図式と pointed 全空間写像の両方を厳密に回収する。
使われ方：一つの元の余錐の図式部分と頂点を、同じ全空間表現から比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 同じ元の図式への制限に沿って、宇宙変更の全空間表現を実際に制限する。 -/
def spaceUniverseRepresentationRestrict {B D : SSet.{u + 1}} [Quasicategory D]
    (F : B ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u}) (g : B ⟶ D) (h : g ≫ G = F) :
    LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection F)) := by
  have := uliftFunctor_preservesCospanLimits.{u + 1, u + 2}
  exact (spaceUniverseTransportRepresentation G).cartesianRestrict
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningMap F G g h))
    ((SSet.uliftFunctor.{u + 2, u + 1}).map g)
    ((leftUnstraighteningMap_isPullback F G g h).map (SSet.uliftFunctor.{u + 2, u + 1}))

/-- 制限した同じ表現の全図式は、元の制限図式の宇宙変更そのもの。 -/
lemma spaceUniverseRepresentationRestrict_diagram {B D : SSet.{u + 1}} [Quasicategory D]
    (F : B ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u}) (g : B ⟶ D) (h : g ≫ G = F) :
    (spaceUniverseRepresentationRestrict F G g h).diagram =
      (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u} := by
  rw [spaceUniverseRepresentationRestrict, LeftTransportRepresentation.cartesianRestrict_diagram]
  change (SSet.uliftFunctor.{u + 2, u + 1}).map g ≫
    ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ spaceUniverseDiagram.{u}) = _
  rw [← Category.assoc, ← Functor.map_comp, h]

/-- 同じ制限の pointed 写像は、元の全空間写像による前合成に厳密に一致する。 -/
lemma spaceUniverseRepresentationRestrict_pointedMap {B D : SSet.{u + 1}} [Quasicategory D]
    (F : B ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u}) (g : B ⟶ D) (h : g ≫ G = F) :
    (spaceUniverseRepresentationRestrict F G g h).pointedMap =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningMap F G g h) ≫
        (spaceUniverseTransportRepresentation G).pointedMap := by
  rw [spaceUniverseRepresentationRestrict, LeftTransportRepresentation.cartesianRestrict_pointedMap]

end SerrePositivity.InfinityCategories.F2.Compact
