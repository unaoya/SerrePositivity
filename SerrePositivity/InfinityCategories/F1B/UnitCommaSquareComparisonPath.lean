module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaSquareDeformation
public import SerrePositivity.InfinityCategories.F1B.ThreeEdgeSquareBoundary

/-!
概要：正方形全体の三辺固定比較から単位比較の経路を取り出す。
方針：右辺の制限を族のホモトピーへ移し、元の図式を厳密に回収する。
規約：境界 path と全体図式の比較で独立な選択をしない。
使われ方：B1 の comma 写像空間から導来 fiber への順方向比較の path 座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位比較の像から指定右辺への経路を正方形全体の変形から取り出す。
方針：三辺固定の比較の右辺を写像空間の族へ転置する。
規約：元の正方形の上下の二単体と、三辺固定の合成の選択を保持する。
使われ方：全体図式の変形と同じ境界 path を使う順方向比較。 -/
noncomputable def unitCommaSquareComparisonHomotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    SSet.Homotopy (unitCommaSquareTargetFamily η x w s ≫
      unitIntervalMap η x (unitCommaFiberTargetVertex G x w)) (unitCommaArrowFamily G x w A) :=
  (unitCommaSquareComparison η x w s).familyHomotopy _ _ rfl
    (congrArg (fun H ↦ curry H.h) (unitCommaArrowFamily_homotopy G x w A)).symm

/-- 概要：単位比較の経路の正方形表示は全体図式の変形の右辺そのもの。
方針：境界の族への転置の回収公式を使う。
規約：経路の類だけでなく二変数の図式の厳密な一致。
使われ方：復元側の境界輸送との照合。 -/
lemma unitCommaSquareComparisonHomotopy_square {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌)
    (w : (unitCommaFiber G x) _⦋0⦌)
    (s : UnitCommaFiberSquare G x (unitCommaSectionVertex η x) w A) :
    intervalFamilySquare (unitCommaSquareComparisonHomotopy η x w s) =
      (unitCommaSquareComparison η x w s).rightSquare :=
  ThreeEdgeSquareComparison.familyHomotopy_square _ _ _ _ _

end SerrePositivity.InfinityCategories
