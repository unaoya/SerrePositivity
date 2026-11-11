module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningSimplexLifts
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationRelativeParameterLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismParameterStart

/-!
概要：coherent な単体の族の持ち上げを、最初の値と部分パラメーター上の持ち上げを保って延長する。
方針：pointed space の射影の left fibration 性と相対パラメーター延長を使う。
規約：底の族は追加パラメーターに依存してよい。最初の値は元の図式 F に固定する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、unstraightening の高次の比較の境界付き延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：追加パラメーター全体で固定した、unstraightening の最初の pointed space 図式。
方針：追加パラメーターを忘れて既存の単体の始点図式へ写す。
規約：定義域は (Δ⁰ ⊗ 元の全空間) ⊗ L。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、相対的な高次の持ち上げの初期条件。 -/
noncomputable def leftUnstraighteningParameterizedSimplexStart {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (L : SSet.{u + 1}) :
    ((Δ[0] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  fst (Δ[0] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningSimplexStart F

/-- 概要：追加パラメーターを持つ coherent な族の初期条件は指定された底の族を被覆する。
方針：最初の値の一般の計算と引き戻しの可換性を使う。
規約：最初の値は追加パラメーターに関して定値な F とする。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、境界付き延長の固定する初期図式の可換性。 -/
lemma leftUnstraighteningParameterizedSimplexStart_projection {B L : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    leftUnstraighteningParameterizedSimplexStart F L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ L) ≫
        (((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ▷ L) ≫ T) := by
  simpa only [leftUnstraighteningParameterizedSimplexStart, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningSimplexStart,
    Category.assoc, pullback.condition, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrism_parameterizedStart (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) F n T h₀).symm

/-- 概要：高次の coherent な族の持ち上げは、指定済みの部分パラメーターと最初の値を保って延長できる。
方針：最初の頂点の prism 包含とパラメーターの単射の相対持ち上げを適用する。
規約：部分パラメーターの単射 j は任意。底 B、K、L の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、境界上の整合性を固定した unstraightening の比較の延長。 -/
lemma exists_leftUnstraighteningSimplexLift_relative_parameters
    {B K L : SSet.{u + 1}} (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (j : K ⟶ L) [Mono j]
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F)
    (u : ((Δ[n] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u})
    (hu₀ : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ K) ≫ u =
      ((Δ[0] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ◁ j) ≫ leftUnstraighteningParameterizedSimplexStart F L)
    (hup : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = ((Δ[n] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ◁ j) ≫
      (((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ▷ L) ≫ T)) :
    ∃ W : ((Δ[n] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      ((Δ[n] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ◁ j) ≫ W = u ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ L) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F L ∧
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = ((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ▷ L) ≫ T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_extend_simplexLift_parameters _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection n j u
    (leftUnstraighteningParameterizedSimplexStart F L)
    (((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ▷ L) ≫ T) hu₀ hup
    (leftUnstraighteningParameterizedSimplexStart_projection F n T h₀)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
