module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningRestrictedLifts
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExtensionCurryComparison

/-!
概要：unstraightening の写像の族は底の制限と関手同型まで可換。
方針：制限する前後の持ち上げを共通の相対延長空間で比較し、その終点を curry する。
規約：比較先は元の底上の相対写像空間。底の射を被覆する全空間の射を用いる。
使われ方：Kerodon Remark 5.6.2.5、Corollary 5.6.0.6、写像空間の比較の底変換の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：unstraightening の普遍的な写像の族は底を保つ。
方針：終点の引き戻しへの持ち上げの第二射影を計算する。
規約：変換の空間のパラメーターを第一射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6、写像の族の制限の底の計算。 -/
lemma leftUnstraighteningMappingFamily_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
      fst _ _ ≫ leftUnstraighteningProjection F := pullback.lift_snd _ _ _

/-- 概要：unstraightening の普遍的な写像の族の pointed space 成分は持ち上げの終点。
方針：終点の引き戻しへの持ち上げの第一射影を計算する。
規約：持ち上げは空間全体について選択したもの。
使われ方：Kerodon Corollary 5.6.0.6、持ち上げの終点と相対写像空間の接続。 -/
lemma leftUnstraighteningMappingFamily_pointed {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingFamily F G ≫ pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷
        leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningTransformationFamilyLift F G := pullback.lift_fst _ _ _

/-- 概要：元の unstraightening の写像の族を制限後の始域に制限する。
方針：始域の全空間の比較射で前合成し、底を保つ式を部分型に記録する。
規約：値域は元の図式 G の全空間。
使われ方：Kerodon Remark 5.6.2.5、底変換の自然性の比較の一辺。 -/
noncomputable def leftUnstraighteningMappingSourceRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    {g : leftUnstraightening (k ≫ F) ⊗ leftUnstraighteningTransformationSpace F G ⟶
        leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst _ _ ≫ leftUnstraighteningProjection (k ≫ F) ≫ k} :=
  ⟨(leftUnstraighteningMap (k ≫ F) F k rfl ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningMappingFamily F G, by
    rw [Category.assoc, leftUnstraighteningMappingFamily_projection,
      whiskerRight_fst_assoc, leftUnstraighteningMap_projection]⟩

/-- 概要：制限後の写像の族を元の変換の空間でパラメーター化し、元の標的へ写す。
方針：変換の制限と標的の全空間の比較射を合成する。
規約：始域・値域・底の図式は始域側の制限と同じ。
使われ方：Kerodon Remark 5.6.2.5、底変換の自然性の比較のもう一辺。 -/
noncomputable def leftUnstraighteningMappingTargetRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    {g : leftUnstraightening (k ≫ F) ⊗ leftUnstraighteningTransformationSpace F G ⟶
        leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst _ _ ≫ leftUnstraighteningProjection (k ≫ F) ≫ k} :=
  ⟨(leftUnstraightening (k ≫ F) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
      leftUnstraighteningMappingFamily (k ≫ F) (k ≫ G) ≫
        leftUnstraighteningMap (k ≫ G) G k rfl, by
    rw [Category.assoc, Category.assoc, leftUnstraighteningMap_projection,
      ← Category.assoc (leftUnstraighteningMappingFamily _ _),
      leftUnstraighteningMappingFamily_projection,
      ← Category.assoc, ← Category.assoc, whiskerLeft_fst]
    rfl⟩

/-- 概要：底変換の前後に作った unstraightening の写像の族は相対 curry の後で関手同型。
方針：二つの普遍的な持ち上げは同じ底と初期値を持つので、可縮な延長空間の終点を比較する。
規約：変換の空間全体がパラメーター。各頂点だけの比較ではない。
使われ方：Kerodon Remark 5.6.2.5、写像空間の比較の底変換に関する自然性。 -/
noncomputable def leftUnstraighteningMappingRestrictionIso {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (relativeFunctorCurry (leftUnstraighteningMappingSourceRestriction F G k).val
        (leftUnstraighteningMappingSourceRestriction F G k).property)
      (relativeFunctorCurry (leftUnstraighteningMappingTargetRestriction F G k).val
        (leftUnstraighteningMappingTargetRestriction F G k).property) := by
  let L := leftUnstraighteningTransformationSpace F G
  let A := leftUnstraightening (k ≫ F)
  let W := leftUnstraighteningRestrictedLift F G k
  let W' := leftUnstraighteningRestrictionLift F G k
  let b := ((Δ[1] ◁ leftUnstraighteningProjection (k ≫ F)) ▷ L) ≫
    ((Δ[1] ⊗ D) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
      leftUnstraighteningTransformationFamily (k ≫ F) (k ≫ G)
  let i := (scaffoldFirstVertex 1 ▷ A) ▷ L
  let v := leftUnstraighteningParameterizedSimplexStart (k ≫ F) L
  let j := simplexPrismVertex 1 1 A ▷ L
  let g := leftUnstraighteningMappingSourceRestriction F G k
  let g' := leftUnstraighteningMappingTargetRestriction F G k
  have hWi : i ≫ W = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, comp_whiskerRight, Category.assoc]
    rw [leftUnstraighteningRestrictedLift_start, whiskerRight_fst_assoc]
    rfl
  have hWi' : i ≫ W' = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, comp_whiskerRight, Category.assoc]
    rw [leftUnstraighteningRestrictionLift_start, whiskerRight_fst_assoc]
    rfl
  have hW : W ≫ pointedSpaceProjection = b :=
    leftUnstraighteningRestrictedLift_projection F G k
  have hW' : W' ≫ pointedSpaceProjection = b :=
    leftUnstraighteningRestrictionLift_projection F G k
  have hv : v ≫ pointedSpaceProjection = i ≫ b := by
    rw [← hWi, Category.assoc, hW]
  have hWj : j ≫ W = g.val ≫ pullback.fst pointedSpaceProjection G := by
    dsimp only [j, W, g, leftUnstraighteningRestrictedLift,
      leftUnstraighteningMappingSourceRestriction]
    rw [← Category.assoc, simplexPrismVertex_parameterizedBaseChange,
      Category.assoc, leftUnstraighteningMappingFamily_pointed]
  have hWj' : j ≫ W' = g'.val ≫ pullback.fst pointedSpaceProjection G := by
    dsimp only [j, W', g', leftUnstraighteningRestrictionLift,
      leftUnstraighteningMappingTargetRestriction]
    rw [← Category.assoc, ← whisker_exchange]
    simp only [Category.assoc]
    rw [leftUnstraighteningMap_pointed, leftUnstraighteningMappingFamily_pointed]
  have hj : j ≫ b =
      (fst A L ≫ leftUnstraighteningProjection (k ≫ F) ≫ k) ≫ G := by
    rw [← hW, ← Category.assoc, hWj, Category.assoc, pullback.condition,
      ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ G) g.property
  exact relativeFunctorExtensionEndpoint_curryIso pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (simplexPrismFirstVertex_leftAnodyne 1 A) L)
    v hv j G (leftUnstraighteningProjection (k ≫ F) ≫ k) hj
    W W' hW hW' hWi hWi' g.val g'.val g.property g'.property hWj hWj'

end SerrePositivity.InfinityCategories
