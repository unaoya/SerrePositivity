module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionThomasonSquare
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomCommaInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.GrothendieckFiberInvariance

/-!
# 元の分解の全右脚の不変性と固定 fiber の包含

概要：任意の可換環上で、元の分解の小さい全右脚図式の各遷移と fiber 包含を反転。
方針：同じ Hom の終域不変性を明示的な小圏の比較で移し、恒等右脚を始対象に使う。
規約：元の代数・全脚・分解を保持。元の対象の cofibrancy は入力しない。
使われ方：同じ Map^h の全単体から三本矢の全図式への元の右射の反転性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.Reedy

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 全右脚の小圏の始対象は元の恒等右脚の up。 -/
def mappingSmallRightSpanInitial (Y : (operad A).Algebra) :
    AsSmall.{u + 1} (algebraRightSpanBase A Y) := by
  let := modelCategory A
  exact AsSmall.up.obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ArrowSpan.rightSliceInitial (trivialCofibrations _) Y)

/-- 元の恒等右脚の始対象性を同じ小圏へ移す。 -/
def mappingSmallRightSpanInitial_isInitial (Y : (operad A).Algebra) :
    IsInitial (mappingSmallRightSpanInitial A Y) := by
  let := modelCategory A
  let h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ArrowSpan.rightSliceInitial_isInitial (trivialCofibrations _) Y
  exact IsInitial.ofUniqueHom (fun t => AsSmall.up.map (h.to (AsSmall.down.obj t))) (by
    intro t f
    apply ULift.ext
    exact h.hom_ext _ _)

/-- 元の分解の小さい全右脚図式の全遷移の nerve は反転される。 -/
lemma mappingSmallResolutionRightDiagram_map_localized_isIso
    {X Y : (operad A).Algebra}
    {s t : AsSmall.{u + 1} (algebraRightSpanBase A Y)} (f : s ⟶ t) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      ((mappingSmallResolutionRightDiagram A X Y).map f).toFunctor)) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj X
  change IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (CostructuredArrow.map
    (S := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram.{u + 1, u, u + 1} q)
    (AsSmall.up.map (AsSmall.down.map f).right))))
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallCommaMap_localized_isIso.{u + 1, u, u + 1} q
    (AsSmall.down.map f).right (mappingRightHomDiagram_map_localized_isIso A (AsSmall.down.map f))

/-- 元の任意の固定右脚の fiber の包含そのものは、同じ全図式で反転される。 -/
lemma mappingResolutionFiberNerveMap_localized_isIso (X Y : (operad A).Algebra)
    (t : AsSmall.{u + 1} (algebraRightSpanBase A Y)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.fiberNerveMap (mappingSmallResolutionRightDiagram A X Y) t)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.fiberNerveMap_localized_isIso (mappingSmallResolutionRightDiagram A X Y)
    (mappingSmallRightSpanInitial_isInitial A Y)
    (mappingSmallResolutionRightDiagram_map_localized_isIso A) t

end SerrePositivity.EInfinity.BarrattEccles
