module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceShapePushout
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberPullbackSquare

/-!
概要：形状の押し出し上の固定頂点の余錐空間を、部分余錐空間の引き戻しで表す。
方針：余錐全体の coslice の引き戻しを頂点 fiber に制限する。
規約：引き戻し表示には単射性は不要。単射な境界側は Kan fibration となる。
使われ方：部分余極限による余錐空間の表現と、貼った余錐の普遍性の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (y : X _⦋0⦌)

/-- 固定頂点の余錐空間でも、形状の押し出しは厳密な引き戻しを与える。 -/
lemma coconeMappingShapePushout_isPullback :
    IsPullback (cosliceRestrictionFiberMap p i y) (cosliceRestrictionFiberMap p j y)
      (cosliceRestrictionFiberMap (i ≫ p) f y)
      (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y) :=
  vertexFiberMap_isPullback (sliceUnderProjection p) (sliceUnderProjection (i ≫ p))
    (sliceUnderProjection (j ≫ p)) (sliceUnderProjection (f ≫ (i ≫ p)))
    (sliceUnderRestrict p i) (sliceUnderRestrict p j) (sliceUnderRestrict (i ≫ p) f)
    (normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p))
    (sliceUnderRestrict_projection p i) (sliceUnderRestrict_projection p j)
    (sliceUnderRestrict_projection (i ≫ p) f)
    (normalizedCoconeRestriction_projection (j ≫ p) g (coconePushoutBoundary_eq hp p))
    (cosliceShapePushout_isPullback hp p) y

/-- 固定頂点の余錐空間を、二つの部分余錐空間の実際の引き戻しとの同型で表す。 -/
def coconeMappingShapePushoutIso :
    coconeMappingSpace p y ≅
      pullback (cosliceRestrictionFiberMap (i ≫ p) f y)
        (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y) :=
  (coconeMappingShapePushout_isPullback hp p y).isoPullback

/-- 単射な境界側の正規化した制限は Kan fibration。 -/
lemma coconeMappingShapePushout_right_fibration [Quasicategory X] [Mono g] :
    Fibration (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y) := by
  rw [normalizedCoconeRestrictionFiber_eq]
  have := coconeMappingSpace_restrict_fibration (j ≫ p) g y
  infer_instance

end
end SerrePositivity.InfinityCategories.HomotopyLimits
