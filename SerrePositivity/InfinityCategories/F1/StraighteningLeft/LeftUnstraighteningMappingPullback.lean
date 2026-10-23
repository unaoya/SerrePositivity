module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullbackSquare

/-!
概要：unstraightening の相対写像空間の底変換と、変換の空間の制限との自然性。
方針：標的の底変換四角形の相対写像空間の同型で、共通の元の底から制限後の底へ戻す。
規約：底変換と分類を同一視する比較は関手同型として保持する。
使われ方：Kerodon Remark 5.6.2.5、Corollary 5.6.0.6、写像空間比較射の底変換四角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：制限後の標的への相対写像空間は、元の標的への相対写像空間と同型。
方針：unstraightening の底変換四角形が引き戻しであることを使う。
規約：始域は制限後の F の全空間で固定する。
使われ方：Kerodon Remark 5.6.2.5、自然性の比較先を制限後の底へ戻す。 -/
noncomputable def leftUnstraighteningMappingPullbackIso {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorSpace (leftUnstraighteningProjection (k ≫ G))
      (leftUnstraighteningProjection (k ≫ F)) ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection (k ≫ F) ≫ k) :=
  relativeFunctorPullbackSquareIso (leftUnstraighteningProjection (k ≫ G))
    (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
    (leftUnstraighteningMap_isPullback (k ≫ G) G k rfl)
    (leftUnstraighteningProjection (k ≫ F))

/-- 概要：unstraightening の相対写像空間を底に沿って制限する。
方針：始域の全空間の射で前合成し、標的の引き戻し四角形で制限後の標的へ戻す。
規約：始域・標的をともに k に沿って制限した相対写像空間へ写す。
使われ方：Kerodon Remark 5.6.2.5、分類の fibration 側の写像空間の底変換。 -/
noncomputable def leftUnstraighteningRelativeRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) ⟶
      relativeFunctorSpace (leftUnstraighteningProjection (k ≫ G))
        (leftUnstraighteningProjection (k ≫ F)) :=
  relativeFunctorOverPre (leftUnstraighteningProjection G) (leftUnstraighteningOverBaseMap F k) ≫
    (leftUnstraighteningMappingPullbackIso F G k).inv

/-- 概要：unstraightening の写像空間比較射は、変換と相対写像空間の底変換と関手同型まで可換。
方針：元の底での自然性に、標的の引き戻し四角形による相対同型の逆射を後合成する。
規約：二辺の終域は制限後の二つの unstraightening の間の相対写像空間。
使われ方：Kerodon Remark 5.6.2.5、Corollary 5.6.0.6、分類の写像空間の自然性四角形。 -/
noncomputable def leftUnstraighteningMappingSpaceMap_restrictionIso
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (leftUnstraighteningMappingSpaceMap F G ≫ leftUnstraighteningRelativeRestriction F G k)
      (leftUnstraighteningTransformationRestriction F G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) := by
  have e : FunctorIso
      (leftUnstraighteningMappingSpaceMap F G ≫
        relativeFunctorOverPre (leftUnstraighteningProjection G)
          (leftUnstraighteningOverBaseMap F k))
      ((leftUnstraighteningTransformationRestriction F G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) ≫
          (leftUnstraighteningMappingPullbackIso F G k).hom) :=
    leftUnstraighteningMappingSpaceMap_baseChangeIso F G k
  have e' := FunctorIso.postcomp e (leftUnstraighteningMappingPullbackIso F G k).inv
  simpa only [leftUnstraighteningRelativeRestriction, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using e'

end SerrePositivity.InfinityCategories
