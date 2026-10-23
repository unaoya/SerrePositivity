module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningRelativeSimplexLifts
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily

/-!
概要：coherent な変換の空間全体を、元の unstraightening の pointed space 成分から一括して持ち上げる。
方針：最初の頂点からの包含と追加パラメーターの直積の left anodyne 性を使う。
規約：選択は空間全体に対する一つの単体集合の射として行う。
使われ方：Kerodon Corollary 5.6.0.6、変換の写像空間から相対写像空間への射の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：追加パラメーター全体に依存する coherent な単体の族は、最初の図式を固定して持ち上がる。
方針：最初の頂点の prism 包含と追加パラメーターの直積に相対延長を適用する。
規約：底の族 T は L に依存してよいが、最初の値は F に固定する。
使われ方：Kerodon Corollary 5.6.5.15、変換の空間全体の整合的な持ち上げの存在。 -/
lemma exists_leftUnstraighteningParameterizedSimplexLift {B L : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : (simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    ∃ W : ((Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ L ⟶ PointedSpaceInfinity.{u},
      W ≫ pointedSpaceProjection = ((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T ∧
      ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ L) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F L :=
  exists_relativeFunctorExtension_of_leftAnodyne pointedSpaceProjection
    (((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T)
    ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ L)
    (leftAnodyneExtensions_whiskerRight _
      (simplexPrismFirstVertex_leftAnodyne n (leftUnstraightening F)) L)
    (leftUnstraighteningParameterizedSimplexStart F L)
    (leftUnstraighteningParameterizedSimplexStart_projection F n T h₀)

/-- 概要：変換の空間全体をパラメーターとする、pointed space への持ち上げの族を選ぶ。
方針：普遍的な変換の評価に、始点を固定するパラメーター付き持ち上げの存在を適用する。
規約：各変換に個別に射を選ぶのではなく、変換の空間全体からの族を選ぶ。
使われ方：Kerodon Corollary 5.6.0.6、写像空間上の unstraightening の射を評価で作るための族。 -/
noncomputable def leftUnstraighteningTransformationFamilyLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u} :=
  (exists_leftUnstraighteningParameterizedSimplexLift F 1
    (leftUnstraighteningTransformationFamily F G)
    (leftUnstraighteningTransformationFamily_zero F G)).choose

/-- 概要：変換の空間全体の持ち上げは、元の射影に沿う普遍的な変換の評価を被覆する。
方針：選択したパラメーター付き持ち上げの底上の条件を取り出す。
規約：空間全体を始域とする射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、終点の写像空間への持ち上げの底の計算。 -/
lemma leftUnstraighteningTransformationFamilyLift_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationFamilyLift F G ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G :=
  (exists_leftUnstraighteningParameterizedSimplexLift F 1
    (leftUnstraighteningTransformationFamily F G)
    (leftUnstraighteningTransformationFamily_zero F G)).choose_spec.1

/-- 概要：変換の空間全体の持ち上げの最初の図式は元の pointed space 成分に定値。
方針：選択した持ち上げの初期条件を取り出す。
規約：最初の零単体の因子を含む制限で表す。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の射が元の始点を保つことの確認。 -/
lemma leftUnstraighteningTransformationFamilyLift_zero {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G) :=
  (exists_leftUnstraighteningParameterizedSimplexLift F 1
    (leftUnstraighteningTransformationFamily F G)
    (leftUnstraighteningTransformationFamily_zero F G)).choose_spec.2

/-- 概要：変換の空間全体の持ち上げの始点を元の全空間と変換の空間の直積上で計算する。
方針：零単体の因子を含む初期条件から、その射影の切断で最初の値を取り出す。
規約：元の pointed space 成分は変換のパラメーターに関して定値。
使われ方：Kerodon Corollary 5.6.0.6、空間全体の持ち上げと個別の変換の持ち上げの接続。 -/
lemma leftUnstraighteningTransformationFamilyLift_start {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 0 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G =
        fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
          pullback.fst pointedSpaceProjection F :=
  simplexPrism_initialRestriction 1 _ _ (leftUnstraighteningTransformationFamilyLift_zero F G)

end SerrePositivity.InfinityCategories
