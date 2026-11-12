module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SliceShapePushout
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConeMappingRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.VertexFiberPullbackSquare

/-!
概要：形状の pushout 上の固定頂点の錐空間を、元の二部分の錐空間の引き戻しへ表示する。
方針：全錐の slice の厳密な引き戻しを、同じ頂点の fiber に制限する。
規約：元の頂点・図式を保持、単射性は不要。使われ方：有限形状の極限交換の接着。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A B C D X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (x : X _⦋0⦌)

/-- 固定頂点の錐空間でも、元の形状の pushout は厳密な引き戻しとなる。 -/
lemma coneMappingShapePushout_isPullback :
    IsPullback (coneRestrictionFiberMap p i x) (coneRestrictionFiberMap p j x)
      (coneRestrictionFiberMap (i ≫ p) f x)
      (normalizedConeRestrictionFiber (j ≫ p) g (conePushoutBoundary_eq hp p) x) :=
  HomotopyLimits.vertexFiberMap_isPullback
    (sliceOverProjection p) (sliceOverProjection (i ≫ p))
    (sliceOverProjection (j ≫ p)) (sliceOverProjection (f ≫ (i ≫ p)))
    (sliceOverRestrict p i) (sliceOverRestrict p j) (sliceOverRestrict (i ≫ p) f)
    (normalizedConeRestriction (j ≫ p) g (conePushoutBoundary_eq hp p))
    (SerrePositivity.InfinityCategories.kanSliceOverRestrict_projection p i) (SerrePositivity.InfinityCategories.kanSliceOverRestrict_projection p j)
    (SerrePositivity.InfinityCategories.kanSliceOverRestrict_projection (i ≫ p) f)
    (normalizedConeRestriction_projection (j ≫ p) g (conePushoutBoundary_eq hp p))
    (sliceShapePushout_isPullback hp p) x

/-- 元の固定頂点の全錐空間を、二部分の錐空間の実際の引き戻しへ表示する同型。 -/
def coneMappingShapePushoutIso :
    coneMappingSpace p x ≅ pullback (coneRestrictionFiberMap (i ≫ p) f x)
      (normalizedConeRestrictionFiber (j ≫ p) g (conePushoutBoundary_eq hp p) x) :=
  (coneMappingShapePushout_isPullback hp p x).isoPullback

/-- 引き戻し表示の第一射影は元の第一部分への制限。 -/
lemma coneMappingShapePushoutIso_fst :
    (coneMappingShapePushoutIso hp p x).hom ≫
      pullback.fst (coneRestrictionFiberMap (i ≫ p) f x)
        (normalizedConeRestrictionFiber (j ≫ p) g (conePushoutBoundary_eq hp p) x) =
      coneRestrictionFiberMap p i x :=
  (coneMappingShapePushout_isPullback hp p x).isoPullback_hom_fst

/-- 引き戻し表示の第二射影は元の第二部分への制限。 -/
lemma coneMappingShapePushoutIso_snd :
    (coneMappingShapePushoutIso hp p x).hom ≫
      pullback.snd (coneRestrictionFiberMap (i ≫ p) f x)
        (normalizedConeRestrictionFiber (j ≫ p) g (conePushoutBoundary_eq hp p) x) =
      coneRestrictionFiberMap p j x :=
  (coneMappingShapePushout_isPullback hp p x).isoPullback_hom_snd

/-- 単射な境界側の正規化した制限は Kan fibration。 -/
lemma coneMappingShapePushout_right_fibration [Quasicategory X] [Mono g] :
    Fibration (normalizedConeRestrictionFiber (j ≫ p) g (conePushoutBoundary_eq hp p) x) := by
  rw [normalizedConeRestrictionFiber_eq]
  have := coneMappingSpace_restrict_fibration (j ≫ p) g x
  infer_instance

end SerrePositivity.InfinityCategories.F2
