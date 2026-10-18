module

public import SerrePositivity.KST.DerivedGeometry.LiftedCoefficientComplex
public import SerrePositivity.KST.DerivedGeometry.LinearComplexHomotopy

/-!
# 係数層の複体 dg 圏と元の層複体の比較

概要：宇宙調整した複体 dg 圏の Z⁰ と H⁰ を元の係数加群層の複体・ホモトピー圏と比較する。
方針：一般の複体の比較と ULiftHom の圏同値を合成する。
規約：元の層のコホモロジーを読むための比較を明示する。
使われ方：KST D4・§13 決定11、Toën Derived Azumaya §3.2 の dg 増強。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：層複体の dg 圏の閉次数零は元の全係数層複体の圏と同値。
方針：閉次数零の一般比較と宇宙調整の複体同値の逆を合成する。
規約：各項の準連接性は要求しない。
使われ方：KST D4・§13 決定11の実際の層複体への接続。
-/
def closedComplexEquivalence :
    ClosedCategory CoefficientDGBase.{u} B.Complexes ≌ CochainComplex B.Modules ℤ :=
  (LinearComplex.closedToComplex (C := B.LiftedModules) CoefficientDGBase.{u}).asEquivalence.trans
    B.complexLiftEquivalence.symm

/--
概要：Hom を元へ戻す関手はホモトピー圏でも本質的全射。
方針：元の各複体を上へ持ち上げ、複体同値の単位の同型を商へ送る。
規約：複体の準同型や acyclic 商はまだ使わない。
使われ方：KST D4、Toën §3.2 の H⁰ 比較。
-/
instance liftedDownHomotopy_essSurj :
    ((show B.LiftedModules ⥤ B.Modules from ULiftHom.down).mapHomotopyCategory
      (.up ℤ)).EssSurj where
  mem_essImage K :=
    ⟨(_root_.HomotopyCategory.quotient B.LiftedModules (.up ℤ)).obj
      (B.complexLiftEquivalence.functor.obj K.as),
      ⟨(_root_.HomotopyCategory.quotient B.Modules (.up ℤ)).mapIso
        (B.complexLiftEquivalence.unitIso.app K.as).symm⟩⟩

/--
概要：Hom の宇宙を戻す関手はホモトピー圏の圏同値。
方針：元の比較関手の充満・忠実性と持ち上げによる本質的全射性を使う。
規約：ホモトピー類の射の比較である。
使われ方：KST D4、Toën §3.2 の元の層のホモトピー圏への接続。
-/
instance liftedDownHomotopy_isEquivalence :
    ((show B.LiftedModules ⥤ B.Modules from ULiftHom.down).mapHomotopyCategory
      (.up ℤ)).IsEquivalence where

/--
概要：係数層の複体 dg 圏の H⁰ は元の層複体のホモトピー圏と同値。
方針：一般の H⁰ 比較と Hom を元へ戻すホモトピー圏の同値を合成する。
規約：acyclic の dg 商の H⁰ と導来圏の比較は別途必要。
使われ方：KST D4・§13 決定11、Toën §3.2 の層の dg 増強の検証。
-/
def homotopyComplexEquivalence :
    SerrePositivity.DifferentialGraded.HomotopyCategory CoefficientDGBase.{u} B.Complexes ≌
      _root_.HomotopyCategory B.Modules (.up ℤ) :=
  (LinearComplex.homotopyComparison (C := B.LiftedModules)
    CoefficientDGBase.{u}).asEquivalence.trans
      ((show B.LiftedModules ⥤ B.Modules from ULiftHom.down).mapHomotopyCategory
        (.up ℤ)).asEquivalence

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
