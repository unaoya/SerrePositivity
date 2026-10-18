module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaCompositionPaths
public import SerrePositivity.InfinityCategories.F1B.CompositionSquareComparison
public import SerrePositivity.InfinityCategories.F1B.SquareNormalizationHomotopy
public import SerrePositivity.InfinityCategories.F1B.ThreeEdgeSquareComparison

/-!
概要：単位の基準正方形から元の comma 正方形へ進む二段階の変形。
方針：上側の相対三角形比較を正方形全体へ移し、具体的な正規化を戻す。
規約：二つの変形の中間図式は厳密に同じ。合成は三辺を固定する fiber の中で選ぶ。
使われ方：B1 の比較の逆関係を、正方形全体と右辺の経路を同時に保って検証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基準単位三角形の正方形から、元の上側を補完した正方形への変形。
方針：元の上側の三角形との相対比較を正方形全体へ移す。
規約：下辺・左辺・上辺を固定し、右辺は上側の対角比較そのもの。
使われ方：元の comma 正方形へ進む変形の第一段階。 -/
noncomputable def unitCommaUpperSquareDeformation {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy
      (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle_family η x
        (unitCommaFiberTargetVertex G x w) (unitCommaSquareTargetFamily η x w s))).diagram
      (functorSquareOfCompositionTriangle (unitCommaCompositionSquare η x w s).upperTriangle).diagram :=
  (unitIntervalCompositionTriangle_family η x (unitCommaFiberTargetVertex G x w)
    (unitCommaSquareTargetFamily η x w s)).squareRelativeHomotopy
      (unitCommaCompositionSquare η x w s).upperTriangle

/-- 概要：元の上側を補完した正方形から元の comma 正方形への変形。
方針：具体的な正方形の正規化ホモトピーを適用する。
規約：第一段階の終点と始点が厳密に同じ。
使われ方：元の下側の二単体を保持して元の図式を回収する。 -/
noncomputable def unitCommaLowerSquareDeformation {A X Y : SSet.{u}}
    [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy
      (functorSquareOfCompositionTriangle (unitCommaCompositionSquare η x w s).upperTriangle).diagram
      s.functorSquare :=
  (unitCommaCompositionSquare η x w s).normalizationHomotopy

/-- 概要：第一段階の右辺は既存の上側の対角の比較と厳密に一致する。
方針：正方形へ移した相対比較の右辺の公式を使う。
規約：二つの独立した path の選択ではない。
使われ方：正方形全体の変形と導来 fiber の path を照合する。 -/
lemma unitCommaUpperSquareDeformation_right {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    (prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (unitCommaUpperSquareDeformation η x w s).h = (unitCommaCompositionUpperPath η x w s).h :=
  FunctorCompositionTriangle.squareRelativeHomotopy_right _ _

/-- 概要：第二段階の右辺は元の下側二単体の具体的な右ホモトピー。
方針：正規化ホモトピーの右辺の公式を使う。
規約：既存の二辺固定比較で選んだ下側 path との同一視はここでは主張しない。
使われ方：二つの経路の整合性を検証するための正確な式。 -/
lemma unitCommaLowerSquareDeformation_right {A X Y : SSet.{u}}
    [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    (prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (unitCommaLowerSquareDeformation η x w s).h =
        rightHomotopySquare ≫ squareTriangle 1 ≫ s.functorSquare :=
  FunctorCompositionSquare.normalizationHomotopy_right _

/-- 概要：基準の単位正方形から元の comma 正方形へ進む三辺固定の比較。
方針：元の二段階の変形を三辺への制限の fiber 内で合成する。
規約：合成のホモトピー・固定条件・元の二段階との合成三角形を同時に持つ。
使われ方：復元側の境界 path の輸送と元の comma 正方形の比較。 -/
noncomputable def unitCommaSquareComparison {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    ThreeEdgeSquareComparison (unitIntervalCompositionTriangle_family η x
      (unitCommaFiberTargetVertex G x w) (unitCommaSquareTargetFamily η x w s))
      (unitCommaCompositionSquare η x w s) :=
  threeEdgeSquareComparison _ _

end SerrePositivity.InfinityCategories
