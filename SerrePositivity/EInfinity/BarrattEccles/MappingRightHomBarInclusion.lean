module

public import SerrePositivity.EInfinity.BarrattEccles.MappingRightHomBarComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarValueInclusion

/-!
# 元の固定右脚の Hom から全右脚の bar への包含

概要：任意の可換環上で、指定した元の右脚の Hom の bar への包含を反転する。
方針：恒等右脚の始対象性と全遷移の不変性を、同じ値の包含の定理へ代入する。
規約：指定右脚・元の分解・全単体を保持する。元の代数の cofibrancy は仮定しない。
使われ方：元の固定右端から全図式の nerve への比較の bar 側の工程。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ分解を用いた、元の指定右脚の全単体の包含。 -/
def mappingRightHomBarInclusion (X Y : (operad A).Algebra)
    (t : algebraRightSpanBase A Y) :
    SSet.uliftFunctor.{u + 1, u}.obj ((mappingRightHomDiagram A X Y).obj t) ⟶
      (BarConstruction.functor (algebraRightSpanBase A Y)).obj
        (mappingRightHomDiagram A X Y) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion (mappingRightHomDiagram A X Y) t

/-- 全次数で同じ指定右脚と元の Hom の単体を一定の射列にする。 -/
lemma mappingRightHomBarInclusion_app (X Y : (operad A).Algebra)
    (t : algebraRightSpanBase A Y) (n : SimplexCategoryᵒᵖ)
    (x : ((mappingRightHomDiagram A X Y).obj t).obj n) :
    (mappingRightHomBarInclusion A X Y t).app n (ULift.up x) =
      (Functor.const _).obj
        (((mappingRightHomDiagram A X Y).flip.obj n).elementsMk t x) := rfl

/-- 元の全ての指定右脚で、その同じ bar への包含そのものが反転される。 -/
lemma mappingRightHomBarInclusion_localized_isIso (X Y : (operad A).Algebra)
    (t : algebraRightSpanBase A Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingRightHomBarInclusion A X Y t)) := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.valueInclusion_localized_isIso (mappingRightHomDiagram A X Y)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations _) Y)
    (fun f => mappingRightHomDiagram_map_localized_isIso A f) t

end SerrePositivity.EInfinity.BarrattEccles
