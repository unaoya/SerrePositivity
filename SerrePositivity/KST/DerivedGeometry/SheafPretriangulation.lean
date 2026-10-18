module

public import SerrePositivity.KST.DerivedGeometry.LinearPretriangulation
public import SerrePositivity.KST.DerivedGeometry.ResolvedSheafComparison
public import SerrePositivity.KST.DerivedGeometry.DGResolution.QuotientRepresentability

/-!
概要：係数加群層の複体とその分解後の acyclic 商の H⁰ を前三角化と比較する。
方針：元の層の有限直和を宇宙調整へ移し、一般の代表可能性の証明を適用する。
規約：Mathlib 導来圏との局所化の比較は別の段階として残す。
使われ方：Drinfeld §2.4・Lemma 13.5・Thm 3.4、KST D4・§10-7、Toën §3.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
open CategoryTheory Limits AlgebraicGeometry
open SerrePositivity.DifferentialGraded
variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：宇宙調整した係数加群層の圏は零対象を持つ。
方針：元の層の圏からの加法的関手で零対象を送る。
規約：層を別の加群の圏へ置き換えない。
使われ方：Drinfeld §2.4、KST D4 の複体の零対象の代表可能性。
-/
instance liftedModulesHasZeroObject : HasZeroObject B.LiftedModules :=
  (show B.Modules ⥤ B.LiftedModules from ULiftHom.up).hasZeroObject_of_additive

/--
概要：宇宙調整した係数加群層の圏は有限直和を持つ。
方針：加法的な圏同値の本質的全射性で有限積を移し、有限直和を得る。
規約：元の層の加法構造と既存の ULiftHom の同値を使う。
使われ方：Drinfeld §2.4、KST D4 の複体の有限和と cone。
-/
instance liftedModulesHasFiniteBiproducts : HasFiniteBiproducts B.LiftedModules := by
  let : (show B.Modules ⥤ B.LiftedModules from ULiftHom.up).EssSurj :=
    (ULiftHom.equiv : B.Modules ≌ B.LiftedModules).essSurj_functor
  let : HasFiniteProducts B.LiftedModules :=
    (show B.Modules ⥤ B.LiftedModules from ULiftHom.up).hasFiniteProducts_of_additive_of_essSurj
  exact HasFiniteBiproducts.of_hasFiniteProducts

/--
概要：宇宙調整した係数加群層の圏は二項直和を持つ。
方針：証明済みの有限直和から既存の二項直和の構成を使う。
規約：同じ層の圏に構造を供給する。
使われ方：Drinfeld §2.4、KST D4 の複体の cone。
-/
instance liftedModulesHasBinaryBiproducts : HasBinaryBiproducts B.LiftedModules :=
  hasBinaryBiproducts_of_finite_biproducts _

/--
概要：層複体 dg 圏の H⁰ はその前三角化の全対象を表現する。
方針：一般の線形加法圏の複体での有限 cell の帰納証明を適用する。
規約：有界性や項ごとの準連接性は仮定しない。
使われ方：Drinfeld §2.4、KST D4・§13 決定11。
-/
instance complexesYonedaToTria_essSurj :
    (DGResolution.yonedaToTria CoefficientDGBase.{u} B.Complexes).EssSurj :=
  LinearComplex.complexYonedaToTria_essSurj CoefficientDGBase.{u}

/--
概要：分解後の acyclic 商自体の H⁰ と、その前三角化の同値。
方針：元の層複体の代表可能性、増大準同値、K-flat な商の比較を合成する。
規約：H⁰ と tria の定義による同一視でも冪等完備化でもない。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4・§10-7、Toën §3.2。
-/
def derivedDGHomotopyTriaEquivalence :
    HomotopyCategory CoefficientDGBase.{u} B.DerivedDG ≌
      TriaCategory CoefficientDGBase.{u} B.DerivedDG :=
  DGResolution.quotientHomotopyTriaEquivalence CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：層の acyclic dg 商自体の H⁰ と元の tria の指定 Verdier 商の同値。
方針：商の H⁰ と tria の証明済み同値を、分解の Verdier 移送と合成する。
規約：Mathlib 導来圏との比較および三角構造の比較は別途検証する。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4・§13 決定11。
-/
def derivedDGHomotopyVerdierEquivalence :
    HomotopyCategory CoefficientDGBase.{u} B.DerivedDG ≌
      TriaQuotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes :=
  B.derivedDGHomotopyTriaEquivalence.trans B.derivedDGTriaEquivalence

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
