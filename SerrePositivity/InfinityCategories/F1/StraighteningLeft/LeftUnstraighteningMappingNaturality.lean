module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：unstraightening の写像空間比較射の底変換に関する自然性。
方針：底上の前合成と底を変える後合成の評価式で、族の比較を比較射そのものへ移す。
規約：自然性は変換の空間全体からの射の間の関手同型として表す。
使われ方：Kerodon Remark 5.6.2.5、Corollary 5.6.0.6、分類の写像空間上の底変換の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底の制限の全空間の比較射を元の底上の射として表示する。
方針：制限後の射影に k を合成し、全空間の比較射の底上の式を用いる。
規約：Over 圏の底は元の B。
使われ方：Kerodon Remark 5.6.2.5、写像空間比較射への前合成を指定する。 -/
noncomputable def leftUnstraighteningOverBaseMap {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    Over.mk (leftUnstraighteningProjection (k ≫ F) ≫ k) ⟶
      Over.mk (leftUnstraighteningProjection F) :=
  Over.homMk (leftUnstraighteningMap (k ≫ F) F k rfl)
    (leftUnstraighteningMap_projection (k ≫ F) F k rfl)

/-- 概要：元の写像空間比較射の全空間での前合成は、始域を制限した族の相対 curry。
方針：相対 uncurry で前合成の評価式を使う。
規約：底の図式は制限後の射影に k を合成したもの。
使われ方：Kerodon Remark 5.6.2.5、族で証明した自然性の前合成側への移送。 -/
lemma leftUnstraighteningMappingSourceRestriction_curry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningMappingSpaceMap F G ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap F k) =
    relativeFunctorCurry (leftUnstraighteningMappingSourceRestriction F G k).val
      (leftUnstraighteningMappingSourceRestriction F G k).property := by
  apply relativeFunctorUncurry_injective
  rw [relativeFunctorUncurry_curry]
  have h := relativeFunctorOverPre_uncurry (leftUnstraighteningProjection G)
    (leftUnstraighteningOverBaseMap F k) (leftUnstraighteningMappingSpaceMap F G)
  rw [leftUnstraighteningMappingSpaceMap_uncurry] at h
  exact h

/-- 概要：制限後の写像空間比較射の全空間での後合成は、標的を戻した族の相対 curry。
方針：相対 uncurry のパラメーター自然性と可換四角形の後合成の評価式を使う。
規約：変換の空間への制限射で始域を元の変換の空間に揃える。
使われ方：Kerodon Remark 5.6.2.5、族で証明した自然性の後合成側への移送。 -/
lemma leftUnstraighteningMappingTargetRestriction_curry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningTransformationRestriction F G k ≫
      leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) ≫
        relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
          (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
          (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
          (leftUnstraighteningProjection (k ≫ F)) =
    relativeFunctorCurry (leftUnstraighteningMappingTargetRestriction F G k).val
      (leftUnstraighteningMappingTargetRestriction F G k).property := by
  apply relativeFunctorUncurry_injective
  rw [relativeFunctorSquarePost_uncurry, relativeFunctorUncurry_naturality,
    leftUnstraighteningMappingSpaceMap_uncurry, relativeFunctorUncurry_curry]
  rfl

/-- 概要：unstraightening の写像空間比較射は底変換と関手同型まで可換。
方針：二辺を相対 curry した写像族に同定し、共通の相対延長による比較を使う。
規約：比較は各変換の頂点でなく写像空間全体における関手同型。
使われ方：Kerodon Remark 5.6.2.5、Corollary 5.6.0.6、分類の写像空間での自然性。 -/
noncomputable def leftUnstraighteningMappingSpaceMap_baseChangeIso
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (leftUnstraighteningMappingSpaceMap F G ≫
        relativeFunctorOverPre (leftUnstraighteningProjection G)
          (leftUnstraighteningOverBaseMap F k))
      ((leftUnstraighteningTransformationRestriction F G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) ≫
          relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
            (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
            (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
            (leftUnstraighteningProjection (k ≫ F))) := by
  rw [leftUnstraighteningMappingSourceRestriction_curry,
    leftUnstraighteningMappingTargetRestriction_curry]
  exact leftUnstraighteningMappingRestrictionIso F G k

end SerrePositivity.InfinityCategories
