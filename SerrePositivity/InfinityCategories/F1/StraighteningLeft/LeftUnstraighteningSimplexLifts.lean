module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening

/-!
概要：単体でパラメーター付けられた coherent な変換の始点を固定した持ち上げ。
方針：最初の頂点からの包含の left anodyne 性と相対延長の可縮な選択空間を使う。
規約：全次元と任意の底を扱う。選択した射の族の厳密な関手性は別に構成する。
使われ方：Kerodon Corollary 5.6.5.15、unstraightening の高次の変換と相対延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体の最初の頂点で固定する pointed space の図式。
方針：零単体の因子を忘れて元の unstraightening の pointed space 成分を取る。
規約：定義域は Δ⁰ と元の全空間の直積。
使われ方：Kerodon Corollary 5.6.5.15、高次の変換の持ち上げの始点条件。 -/
noncomputable def leftUnstraighteningSimplexStart {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    (Δ[0] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  snd (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) ≫ pullback.fst pointedSpaceProjection F

/-- 概要：高次の変換の始点の pointed space 図式は指定した底の族を被覆する。
方針：prism の最初の頂点の分解とその自然性を使い、引き戻しの可換性へ帰着する。
規約：変換の最初の値が F であることを仮定する。
使われ方：Kerodon Corollary 5.6.5.15、相対延長の始点と底の整合性。 -/
lemma leftUnstraighteningSimplexStart_projection {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    leftUnstraighteningSimplexStart F ≫ pointedSpaceProjection =
      (scaffoldFirstVertex n ▷ leftUnstraightening F) ≫
        ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T) := by
  rw [leftUnstraighteningSimplexStart, Category.assoc, pullback.condition,
    scaffoldFirstVertex_whiskerRight, Category.assoc,
    ← Category.assoc (simplexPrismVertex n 0 (leftUnstraightening F)),
    simplexPrismVertex_naturality, Category.assoc, h₀]
  rfl

/-- 概要：高次の coherent な変換の始点と底の族を固定した持ち上げの選択空間。
方針：最初の頂点の直積からの相対延長の空間を取る。
規約：n は任意。始点の全空間は変換のパラメーターとは別に保持する。
使われ方：Kerodon Corollary 5.6.5.15、高次の整合的な持ち上げの選択。 -/
noncomputable def leftUnstraighteningSimplexChoiceSpace {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection
    ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T)
    (scaffoldFirstVertex n ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F n T h₀)

/-- 概要：高次の coherent な変換の始点を固定した持ち上げの選択空間は可縮な Kan 複体。
方針：最初の頂点と任意のパラメーターの積の left anodyne 性を使う。
規約：単なる頂点の非空性ではなく全高次の選択の可縮性を主張する。
使われ方：Kerodon Corollary 5.6.5.15、unstraightening の高次の持ち上げの存在と一意性。 -/
lemma leftUnstraighteningSimplexChoiceSpace_isContractibleKan {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    IsContractibleKan (leftUnstraighteningSimplexChoiceSpace F n T h₀) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection _ _
    (simplexPrismFirstVertex_leftAnodyne n (leftUnstraightening F)) _ _

/-- 概要：高次の coherent な変換は元の unstraightening の全空間から、最初の値を固定して持ち上がる。
方針：相対延長を選び、零単体の因子の射影の切断で始点条件を回収する。
規約：底の族と最初の pointed space 成分を厳密に保つ。
使われ方：Kerodon Corollary 5.6.5.15、高次の比較を構成する実際の持ち上げ。 -/
lemma exists_leftUnstraighteningSimplexLift {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    ∃ W : (Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u},
      W ≫ pointedSpaceProjection = (Δ[n] ◁ leftUnstraighteningProjection F) ≫ T ∧
      simplexPrismVertex n 0 (leftUnstraightening F) ≫ W = pullback.fst pointedSpaceProjection F := by
  obtain ⟨W, hWp, hW₀⟩ := exists_relativeFunctorExtension_of_leftAnodyne pointedSpaceProjection
    ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T)
    (scaffoldFirstVertex n ▷ leftUnstraightening F)
    (simplexPrismFirstVertex_leftAnodyne n (leftUnstraightening F))
    (leftUnstraighteningSimplexStart F) (leftUnstraighteningSimplexStart_projection F n T h₀)
  refine ⟨W, hWp, ?_⟩
  have h := congrArg (fun k => simplexPrismVertex 0 0 (leftUnstraightening F) ≫ k) hW₀
  simpa only [scaffoldFirstVertex_whiskerRight, leftUnstraighteningSimplexStart,
    ← Category.assoc, simplexPrismVertex_snd, Category.id_comp] using h

end SerrePositivity.InfinityCategories
