module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionThomasonSquare
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonInversion

/-!
# 元の全右脚の二つの Thomason 比較射の反転性

概要：任意の可換環上で、分解側と全左脚側の同じ全右脚図式の比較を反転する。
方針：同じ元の図式を、小さい Cat 値図式の Thomason 定理に代入する。
規約：元の代数の cofibrancy や単体集合モデルは入力しない。
使われ方：元の Map^h の bar と三本矢の全図式への比較の正方形。
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

/-- 全右脚を走る元の分解の Thomason 射そのものが反転される。 -/
lemma mappingResolutionThomason_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (mappingSmallResolutionRightDiagram A X Y))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_localized_isIso (mappingSmallResolutionRightDiagram A X Y)

/-- 全右脚を走る元の全左脚の Thomason 射そのものも反転される。 -/
lemma mappingSpanThomason_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (mappingSmallSpanRightDiagram A X Y))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_localized_isIso (mappingSmallSpanRightDiagram A X Y)

end SerrePositivity.EInfinity.BarrattEccles
