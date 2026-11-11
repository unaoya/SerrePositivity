module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening

/-!
概要：単体でパラメーター付けられた coherent な変換の始点を固定した持ち上げ。
方針：最初の頂点からの包含の left anodyne 性と相対延長の可縮な選択空間を使う。
規約：全次元と任意の底を扱う。選択した射の族の厳密な関手性は別に構成する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、unstraightening の高次の変換と相対延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：単体の最初の頂点で固定する pointed space の図式。
方針：零単体の因子を忘れて元の unstraightening の pointed space 成分を取る。
規約：定義域は Δ⁰ と元の全空間の直積。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、高次の変換の持ち上げの始点条件。 -/
noncomputable def leftUnstraighteningSimplexStart {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (Δ[0] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  snd (Δ[0] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F

/-- 概要：高次の変換の始点の pointed space 図式は指定した底の族を被覆する。
方針：prism の最初の頂点の分解とその自然性を使い、引き戻しの可換性へ帰着する。
規約：変換の最初の値が F であることを仮定する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、相対延長の始点と底の整合性。 -/
lemma leftUnstraighteningSimplexStart_projection {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ≫ T = F) :
    leftUnstraighteningSimplexStart F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ≫
        ((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ T) := by
  rw [leftUnstraighteningSimplexStart, Category.assoc, pullback.condition,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex_naturality, Category.assoc, h₀]
  rfl

/-- 概要：高次の coherent な変換の始点と底の族を固定した持ち上げの選択空間。
方針：最初の頂点の直積からの相対延長の空間を取る。
規約：n は任意。始点の全空間は変換のパラメーターとは別に保持する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、高次の整合的な持ち上げの選択。 -/
noncomputable def leftUnstraighteningSimplexChoiceSpace {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ≫ T = F) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    ((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F n T h₀)

/-- 概要：高次の coherent な変換の始点を固定した持ち上げの選択空間は可縮な Kan 複体。
方針：最初の頂点と任意のパラメーターの積の left anodyne 性を使う。
規約：単なる頂点の非空性ではなく全高次の選択の可縮性を主張する。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、unstraightening の高次の持ち上げの存在と一意性。 -/
lemma leftUnstraighteningSimplexChoiceSpace_isContractibleKan {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ≫ T = F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (leftUnstraighteningSimplexChoiceSpace F n T h₀) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne n (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F)) _ _

/-- 概要：高次の coherent な変換は元の unstraightening の全空間から、最初の値を固定して持ち上がる。
方針：相対延長を選び、零単体の因子の射影の切断で始点条件を回収する。
規約：底の族と最初の pointed space 成分を厳密に保つ。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、高次の比較を構成する実際の持ち上げ。 -/
lemma exists_leftUnstraighteningSimplexLift {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 B ≫ T = F) :
    ∃ W : (Δ[n] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ T ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ≫ W = pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F := by
  obtain ⟨W, hWp, hW₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.exists_relativeFunctorExtension_of_leftAnodyne _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    ((Δ[n] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne n (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F))
    (leftUnstraighteningSimplexStart F) (leftUnstraighteningSimplexStart_projection F n T h₀)
  refine ⟨W, hWp, ?_⟩
  have h := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 0 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ≫ k) hW₀
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, leftUnstraighteningSimplexStart,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex_snd, Category.id_comp] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
