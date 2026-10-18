module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistEquivalence
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeDerivedExtensionSquare
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraCartesianConditions
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianEnhancement
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
概要：KST §3.1 の全整数捻りを cartesian perfect 導来部分圏の自己同値に制限する。
方針：canonical な係数拡大比較の可逆性の同値を元の Koszul 表示へ移す。
規約：全対象の対象条件を保存・反映する。層レベルの比較は別工程。
使われ方：導来 blowup の生成系と半直交分解に使う逆捻り。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：整数捻りは元の Koszul 表示で全導来対象の cartesian 性を保存・反映する。
方針：一般 gauge の指定比較の同値と、正規表示との可逆性比較を合成する。
規約：KST §3.1。使われ方：既存の cartesian 部分圏への捻り作用。 -/
theorem finiteOverlapDerivedTwistAction_cartesian_iff (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramCartesian R a ((finiteOverlapDerivedTwistAction R a m).obj X) ↔
      diagramCartesian R a X :=
  (finiteOverlapAlgebraCartesian_iff R a _).symm.trans
    ((diagramGaugeDerivedAction_cartesian_iff (finiteOverlapDGAlgebraDiagram R a)
      (finiteOverlapTwistGauge R a m) X).trans (finiteOverlapAlgebraCartesian_iff R a X))

/-- 概要：整数捻りは元の Koszul 表示で全導来対象の cartesian perfect 性を保存・反映。
方針：指定比較の可逆性と局所 perfect 条件の両方向の同値を合わせる。
規約：KST §3.1。使われ方：大域 Perf 候補の全対象への捻り作用。 -/
theorem finiteOverlapDerivedTwistAction_cartesianPerfect_iff (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    diagramCartesianPerfect R a ((finiteOverlapDerivedTwistAction R a m).obj X) ↔
      diagramCartesianPerfect R a X :=
  and_congr (finiteOverlapDerivedTwistAction_cartesian_iff R a m X)
    (finiteOverlapDerivedTwistAction_locallyPerfect_iff R a m X)

/-- 概要：整数捻りによる既存の cartesian perfect 導来部分圏の自己同値。
方針：全導来圏の指定自己同値を、保存・反映する対象条件で制限する。
規約：KST §3.1、元の Koszul 模型と指定対象条件を保つ。
使われ方：生成系と半直交分解で用いる大域の逆捻り。 -/
def blowupDerivedTwistEquivalence (m : ℤ) :
    CartesianPerfectDerivedDiagramModules R a ≌ CartesianPerfectDerivedDiagramModules R a :=
  (finiteOverlapDerivedTwistEquivalence R a m).congrFullSubcategory
    (P := diagramCartesianPerfect R a) (Q := diagramCartesianPerfect R a)
    (by
      funext X
      exact propext (finiteOverlapDerivedTwistAction_cartesianPerfect_iff R a m X))

/-- 概要：制限した捻り自己同値の underlying 対象は元の導来捻り作用の値。
方針：充満部分圏への制限の対象の定義を読む。
規約：KST §3.1。使われ方：部分圏の計算を全導来圏へ戻す。 -/
theorem blowupDerivedTwistEquivalence_obj (m : ℤ)
    (X : CartesianPerfectDerivedDiagramModules R a) :
    (diagramCartesianPerfect R a).ι.obj ((blowupDerivedTwistEquivalence R a m).functor.obj X) =
      (finiteOverlapDerivedTwistAction R a m).obj X.obj := rfl

/-- 概要：制限した捻り自己同値の underlying 射は元の導来作用で送った射。
方針：充満部分圏への持ち上げは射を変えない。
規約：KST §3.1。使われ方：捻りによる Hom 比較を指定作用と接続する。 -/
theorem blowupDerivedTwistEquivalence_map (m : ℤ)
    {X Y : CartesianPerfectDerivedDiagramModules R a} (f : X ⟶ Y) :
    (diagramCartesianPerfect R a).ι.map ((blowupDerivedTwistEquivalence R a m).functor.map f) =
      (finiteOverlapDerivedTwistAction R a m).map ((diagramCartesianPerfect R a).ι.map f) := rfl

end SerrePositivity.KST.DerivedBlowup
