module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpanDiagram
public import SerrePositivity.EInfinity.FrameHom.BarInitialComparison

/-!
# 元の恒等右脚から全右脚の Hom の bar への比較

概要：任意の可換環上の同じ分解の Hom 図式へ bar の不変性を代入する。
方針：恒等右脚の始対象性と、全遷移の終域不変性を使う。
規約：元の全代数・分解・右脚を保ち、単体集合モデルを仮定しない。
使われ方：固定右脚から全図式への比較の定値図式側の反転。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の恒等右脚から全右脚の Hom への自然変換。 -/
def mappingRightHomFromIdentity (X Y : (operad A).Algebra) :
    let := modelCategory A
    (Functor.const (algebraRightSpanBase A Y)).obj
        ((mappingRightHomDiagram A X Y).obj
          (FrameHom.ArrowSpan.rightSliceInitial (trivialCofibrations _) Y)) ⟶
      mappingRightHomDiagram A X Y := by
  let := modelCategory A
  exact FrameHom.BarRows.fromInitial (mappingRightHomDiagram A X Y)
    (FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations _) Y)

/-- 各成分は元の右脚そのものによる後合成。 -/
lemma mappingRightHomFromIdentity_app (X Y : (operad A).Algebra)
    (t : algebraRightSpanBase A Y) :
    let := modelCategory A
    (mappingRightHomFromIdentity A X Y).app t =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        ((SerrePositivity.Reedy.cosimplicialResolutionFamily
          (mappingCofibrantFactorization A)).obj.obj X)).map t.hom := rfl

/-- 元の定値図式から全右脚への bar の比較は anodyne 反転後に可逆。 -/
lemma mappingRightHomFromIdentity_bar_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((BarConstruction.functor (algebraRightSpanBase A Y)).map
        (mappingRightHomFromIdentity A X Y))) := by
  let := modelCategory A
  exact FrameHom.BarRows.fromInitial_localized_isIso (mappingRightHomDiagram A X Y)
    (FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations _) Y)
    (fun f => mappingRightHomDiagram_map_localized_isIso A f)

end SerrePositivity.EInfinity.BarrattEccles
