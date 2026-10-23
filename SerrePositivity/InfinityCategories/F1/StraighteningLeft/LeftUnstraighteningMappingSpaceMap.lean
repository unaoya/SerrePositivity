module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFamilyLifts
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：coherent な変換の写像空間から、unstraightening 間の底上の相対写像空間への射。
方針：変換の空間全体の持ち上げを終点で評価し、標的の引き戻しへ入れて相対 curry する。
規約：全次数での単体集合の射を構成する。同値性は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6、coherent な変換と fibration の相対写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：変換の空間全体の持ち上げの終点は、元の射影の後の標的図式 G を被覆する。
方針：持ち上げの底の式と普遍的な変換の終点条件を合成する。
規約：変換の空間のパラメーターは第一射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6、終点の族を標的の unstraightening へ入れる条件。 -/
lemma leftUnstraighteningTransformationFamilyLift_one_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G) ≫ pointedSpaceProjection =
      (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningProjection F) ≫ G := by
  rw [Category.assoc, leftUnstraighteningTransformationFamilyLift_projection,
    ← Category.assoc, simplexPrismVertex_parameterizedBaseChange,
    leftUnstraighteningTransformationFamily_one, whiskerRight_fst_assoc, Category.assoc]

/-- 概要：変換の空間全体の持ち上げの終点は、unstraightening 間の底上の射の族となる。
方針：終点の pointed space 成分と元の底への射影を標的の引き戻しへ持ち上げる。
規約：変換の空間は評価のパラメーターとして残す。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射の相対 uncurry。 -/
noncomputable def leftUnstraighteningMappingFamily {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraightening F ⊗ leftUnstraighteningTransformationSpace F G ⟶ leftUnstraightening G :=
  pullback.lift
    ((simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G)
    (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningProjection F)
    (leftUnstraighteningTransformationFamilyLift_one_projection F G)

/-- 概要：coherent な変換の区間写像空間から、unstraightening 間の相対写像空間への単体集合の射。
方針：空間全体を持ち上げた終点の底上の族を相対 curry する。
規約：底 B は任意。同値性や厳密な恒等・合成則はこの定義には含めない。
使われ方：Kerodon Corollary 5.6.0.6、変換の写像空間と fibration の写像空間の実際の比較射。 -/
noncomputable def leftUnstraighteningMappingSpaceMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace F G ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) :=
  relativeFunctorCurry (leftUnstraighteningMappingFamily F G) (pullback.lift_snd _ _ _)

/-- 概要：写像空間の比較を相対 uncurry すると、全変換の持ち上げの終点の底上の族となる。
方針：相対 curry と uncurry の往復を使う。
規約：選択した普遍的な持ち上げの族そのものとの等式。
使われ方：Kerodon Corollary 5.6.0.6、比較射の評価と具体的な持ち上げの接続。 -/
lemma leftUnstraighteningMappingSpaceMap_uncurry {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) =
      leftUnstraighteningMappingFamily F G :=
  relativeFunctorUncurry_curry _ _

/-- 概要：写像空間の比較の評価を pointed space 成分で見ると、普遍的な持ち上げの終点に一致する。
方針：相対 curry の往復と引き戻しの第一射影の計算を使う。
規約：全変換の空間をパラメーターとする等式。
使われ方：Kerodon Corollary 5.6.0.6、変換の写像空間の比較の終点の計算。 -/
lemma leftUnstraighteningMappingSpaceMap_pointed {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) ≫
      pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamilyLift F G := by
  rw [leftUnstraighteningMappingSpaceMap_uncurry, leftUnstraighteningMappingFamily, pullback.lift_fst]

/-- 概要：coherent な図式の右 pinched 写像空間から、unstraightening 間の相対写像空間への射。
方針：右 pinched 模型から区間模型への既存の比較の後に、普遍的な持ち上げの終点の射を合成する。
規約：底 B は任意。同値性は後続の証明課題。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式の標準的な写像空間からの実際の比較射。 -/
noncomputable def leftUnstraighteningPinchedMappingSpaceMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    pinchedHom (functorVertex F) (functorVertex G) ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) :=
  pinchedHomToIntervalMappingSpace (functorVertex F) (functorVertex G) ≫
    leftUnstraighteningMappingSpaceMap F G

/-- 概要：右 pinched 模型の unstraightening 比較の同値性は区間模型の比較の同値性と同値。
方針：模型間の既存の同値と二対三則を使う。
規約：この判定だけから比較の同値性自体は主張しない。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の写像空間の同値性の証明を区間模型で行う。 -/
lemma leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningPinchedMappingSpaceMap F G) ↔
      IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G) := by
  have he := pinchedHomToIntervalMappingSpace_isQCatEquivalence (functorVertex F) (functorVertex G)
  exact ⟨fun h => he.cancel_left h, fun h => he.comp h⟩

end SerrePositivity.InfinityCategories
