module

public import SerrePositivity.KST.DerivedGeometry.SheafDerivedComparison
public import SerrePositivity.KST.DerivedGeometry.DGResolution.QuotientComparisonObjects

/-!
概要：層の dg 商の H⁰ と Mathlib 導来圏との比較で各対象の導来像を計算する。
方針：商の代表対象、Verdier 移送、元の層のホモトピー圏、Qh の正方形を合成する。
規約：元の層複体のコホモロジーを同じ関手で読む。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4・§10-7、Toën §3.2 の Dqc。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory AlgebraicGeometry
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) [HasDerivedCategory.{w} B.Modules]

/--
概要：商の H⁰ の対象は、増大像を元の層複体へ戻したものの導来像へ送られる。
方針：同じ対象の代表加群の比較と四つの既存の因子分解同型を合成する。
規約：対象の準連接コホモロジーを別の解消で判定しない。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4・§13 決定11 の Dqc への制限。
-/
def derivedDGHomotopyEquivalence_objIso (K : B.ResolvedComplexes) :
    B.derivedDGHomotopyEquivalence.functor.obj
      ((toHomotopy CoefficientDGBase.{u} B.DerivedDG).obj
        (ForgetEnrichment.of (Complex CoefficientDGBase.{u}) ⟨K⟩)) ≅
      _root_.DerivedCategory.Q.obj
        (B.complexLiftEquivalence.inverse.obj (B.resolvedAugmentation.obj K)) :=
  B.triaDerivedEquivalence.functor.mapIso
    (DGResolution.quotientHomotopyOriginalRepresentableIso CoefficientDGBase.{u} B.Complexes
      B.acyclicComplexes K) ≪≫
    B.triaDerivedSquare.app (triaRepresentable CoefficientDGBase.{u} B.Complexes
      (B.resolvedAugmentation.obj K)) ≪≫
    _root_.DerivedCategory.Qh.mapIso (B.triaHomotopyRepresentableIso (B.resolvedAugmentation.obj K)) ≪≫
    (_root_.DerivedCategory.quotientCompQhIso B.Modules).app
      (B.complexLiftEquivalence.inverse.obj (B.resolvedAugmentation.obj K))

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
