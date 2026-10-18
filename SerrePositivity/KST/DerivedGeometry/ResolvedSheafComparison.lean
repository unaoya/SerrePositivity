module

public import SerrePositivity.KST.DerivedGeometry.SheafDerivedDG
public import SerrePositivity.KST.DerivedGeometry.CoefficientComplexComparison

/-!
# 平坦分解した層複体と acyclic 商の比較

概要：一般 dg 分解の H⁰ と前三角化の移送を、実際の係数加群層の複体へ適用する。
方針：証明済みの増大準同値と分解後の商の三角比較を使う。
規約：商の前三角化の比較と、商自身の H⁰ の導来圏比較は区別する。
使われ方：Drinfeld Lemma 13.5・Thm 3.4・§3.5、KST D4、Toën §3.2。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

open CategoryTheory AlgebraicGeometry
open SerrePositivity.DifferentialGraded

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：層複体の平坦分解の増大関手は H⁰ 上の圏同値を与える。
方針：一般の具体的増大準同値の証明を適用する。
規約：元の層複体の Hom の平坦性は不要。
使われ方：Drinfeld Lemma 13.5、KST D4 の分解の移送。
-/
instance resolvedAugmentation_homotopy_isEquivalence :
    B.resolvedAugmentation.onHomotopy.IsEquivalence :=
  DGResolution.augmentation_homotopy_isEquivalence CoefficientDGBase.{u} B.Complexes

/--
概要：平坦分解の H⁰ は実際の係数加群層のホモトピー圏と同値。
方針：増大準同値の H⁰ 同値と元の層複体への比較を合成する。
規約：acyclic の商をまだ取らない比較。
使われ方：Drinfeld Lemma 13.5、KST D4・§13 決定11。
-/
def resolvedHomotopyComplexEquivalence :
    SerrePositivity.DifferentialGraded.HomotopyCategory CoefficientDGBase.{u}
      B.ResolvedComplexes ≌ _root_.HomotopyCategory B.Modules (.up ℤ) :=
  B.resolvedAugmentation.onHomotopy.asEquivalence.trans B.homotopyComplexEquivalence

/--
概要：平坦分解後の acyclic 商の前三角化と、元の複体 dg 圏の指定商の同値。
方針：一般の分解後の商から元の Verdier 商への比較を適用する。
規約：Mathlib 導来圏との H⁰ 同値はこの宣言には含まない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の導来商の比較。
-/
def derivedDGTriaEquivalence :
    TriaCategory CoefficientDGBase.{u} B.DerivedDG ≌
      TriaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes :=
  DGResolution.quotientToOriginalVerdierEquivalence CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes

/--
概要：層の acyclic 商の前三角化比較の順関手は shift と両立する。
方針：一般の比較の構造を保持する。
規約：冪等完備化しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の三角比較。
-/
instance derivedDGTriaEquivalenceFunctorCommShift :
    B.derivedDGTriaEquivalence.functor.CommShift ℤ :=
  DGResolution.quotientToOriginalVerdierFunctorCommShift CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes

/--
概要：層の acyclic 商の前三角化比較の逆関手は shift と両立する。
方針：一般の逆向き比較の構造を保持する。
規約：同じ shift を使う。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の三角比較。
-/
instance derivedDGTriaEquivalenceInverseCommShift :
    B.derivedDGTriaEquivalence.inverse.CommShift ℤ :=
  DGResolution.quotientToOriginalVerdierInverseCommShift CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes

/--
概要：層の acyclic 商の前三角化比較の随伴は shift と両立する。
方針：一般比較の随伴の整合性を使う。
規約：順逆の構造を独立には選ばない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の三角比較。
-/
instance derivedDGTriaEquivalenceCommShift : B.derivedDGTriaEquivalence.CommShift ℤ :=
  DGResolution.quotientToOriginalVerdierCommShift CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes

/--
概要：層の acyclic 商の前三角化比較は三角同値。
方針：一般比較の平坦性の証明と Verdier 移送をそのまま使う。
規約：元の層の Hom に K-flat 性を仮定しない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4・§13 決定11。
-/
instance derivedDGTriaEquivalenceIsTriangulated : B.derivedDGTriaEquivalence.IsTriangulated :=
  DGResolution.quotientToOriginalVerdierIsTriangulated CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
