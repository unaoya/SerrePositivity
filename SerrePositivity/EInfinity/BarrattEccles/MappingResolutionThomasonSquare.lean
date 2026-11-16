module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionFixedRightComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonNaturality

/-!
# 元の分解と全左脚の比較の Thomason 正方形

概要：全右脚に自然な元の比較を、bar と全図式の nerve の厳密な可換正方形にする。
方針：各固定右脚の反転性を bar へ移し、同じ自然変換の Thomason 自然性を適用。
規約：元の分解・全脚・元の Grothendieck 比較を保持。単体集合モデルは不要。
使われ方：元の Map^h の bar と三本矢の全図式の nerve の比較の接続。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 全右脚上の元の分解の小さい Cat 値図式。 -/
abbrev mappingSmallResolutionRightDiagram (X Y : (operad A).Algebra) :=
  let := modelCategory A
  mappingSmallRightSpanForget A Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram
    (mappingSmallResolutionOverFunctor A X ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionLeftForget.{u + 1, u, u + 1} X)

/-- 全右脚上の全左脚の小さい Cat 値図式。 -/
abbrev mappingSmallSpanRightDiagram (X Y : (operad A).Algebra) :=
  let := modelCategory A
  mappingSmallRightSpanForget A Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionLeftForget.{u + 1, u, u + 1} X)

/-- 元の全右脚の比較と同じ自然変換の nerve の bar の射。 -/
def mappingResolutionBarComparison (X Y : (operad A).Algebra) :=
  (BarConstruction.functor (AsSmall.{u + 1} (algebraRightSpanBase A Y))).map
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveComparison (mappingFixedRightDiagramComparison A X Y))

/-- 全成分の反転性から、元の bar の比較そのものが反転される。 -/
lemma mappingResolutionBarComparison_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingResolutionBarComparison A X Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.map_localized_isIso _
    (mappingFixedRightDiagramComparison_localized_isIso A X Y)

/-- 元の Grothendieck 比較と bar 比較は、同じ二つの Thomason 射で厳密に可換。 -/
lemma mappingResolutionThomasonSquare (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (mappingSmallResolutionRightDiagram A X Y) ≫
        nerveMap (mappingFixedRightGrothendieckComparison A X Y) =
      mappingResolutionBarComparison A X Y ≫
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (mappingSmallSpanRightDiagram A X Y) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_naturality (mappingFixedRightDiagramComparison A X Y)

end SerrePositivity.EInfinity.BarrattEccles
