module

public import SerrePositivity.InfinityCategories.F1.Universe.RelativeFunctor
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap

/-!
概要：coherent な変換の写像空間の比較を小さい unstraightening の相対写像空間へ移す。
方針：相対関手空間の宇宙移送と全空間の縮小同型による厳密な同型を合成する。
規約：写像空間の同値性はまだ仮定せず、その証明課題を同値な形で保持する。
使われ方：Kerodon Corollary 5.6.0.6、小さい left fibrations の ∞ 圏における完全忠実性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい unstraightening の持ち上げと元の全空間は底上の対象として同型。
方針：全空間の縮小同型と射影の可換式を Over 圏に束縛する。
規約：底は元の B の宇宙持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6、縮小同型を相対写像空間へ作用させる。 -/
noncomputable def smallLeftUnstraighteningOverIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)) ≅
      Over.mk (leftUnstraighteningProjection F) :=
  Over.isoMk (smallLeftUnstraighteningIso F) (smallLeftUnstraighteningIso_projection F)

/-- 概要：小さい unstraightening 間の相対写像空間の持ち上げは元の相対写像空間と厳密に同型。
方針：相対関手空間と ULift の交換の後で、二つの全空間の底上の縮小同型を作用させる。
規約：任意の coherent な図式 F と G を扱う。
使われ方：Kerodon Corollary 5.6.0.6、小さい fibration の写像空間で完全忠実性を証明するための移送。 -/
noncomputable def smallLeftUnstraighteningRelativeFunctorIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F)) ≅
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) :=
  uliftRelativeFunctorIso (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F) ≪≫
    relativeFunctorOverIso (smallLeftUnstraighteningOverIso F) (smallLeftUnstraighteningOverIso G)

/-- 概要：coherent な変換の空間から小さい unstraightening の相対写像空間の持ち上げへの比較射。
方針：既存の比較射に相対写像空間の縮小同型の逆を合成する。
規約：比較を頂点ごとの対応に落とさず、全次数の射として保持する。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較を小さい fibration 側の Hom に接続する。 -/
noncomputable def liftedSmallLeftUnstraighteningMappingSpaceMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace F G ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F)) :=
  leftUnstraighteningMappingSpaceMap F G ≫ (smallLeftUnstraighteningRelativeFunctorIso F G).inv

/-- 概要：小さい相対写像空間へ移した比較を元へ戻すと既存の比較射を回収する。
方針：縮小同型の逆と順方向の往復を消す。
規約：元の比較射そのものの厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、比較の評価と同値性を元の構成へ戻す。 -/
lemma liftedSmallLeftUnstraighteningMappingSpaceMap_comparison {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    liftedSmallLeftUnstraighteningMappingSpaceMap F G ≫
      (smallLeftUnstraighteningRelativeFunctorIso F G).hom =
      leftUnstraighteningMappingSpaceMap F G := by
  rw [liftedSmallLeftUnstraighteningMappingSpaceMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 概要：小さい相対写像空間へ移した比較の同値性は元の比較の同値性と同値。
方針：厳密な縮小同型を二対三則で消去する。
規約：この判定は同値性の未証明箇所を解消したという主張ではない。
使われ方：Kerodon Corollary 5.6.0.6、完全忠実性の残る証明課題を小さい Hom で扱う。 -/
lemma liftedSmallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (liftedSmallLeftUnstraighteningMappingSpaceMap F G) ↔
      IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G) := by
  have he : IsQCatEquivalence (smallLeftUnstraighteningRelativeFunctorIso F G).hom :=
    (qCatEquivalenceOfIso (smallLeftUnstraighteningRelativeFunctorIso F G)).isQCatEquivalence
  constructor
  · intro h
    have h' := h.comp he
    rw [liftedSmallLeftUnstraighteningMappingSpaceMap_comparison] at h'
    exact h'
  · intro h
    apply he.cancel_right
    rw [liftedSmallLeftUnstraighteningMappingSpaceMap_comparison]
    exact h

end SerrePositivity.InfinityCategories
