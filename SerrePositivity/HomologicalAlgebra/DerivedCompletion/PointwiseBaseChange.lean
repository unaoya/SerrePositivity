module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# 各項の H⁰ 完備化と係数拡大

## 概要
加群の H⁰ 主完備化を加法的な関手にし、通常の係数拡大との合成を固定する。

## 方針
標準の single 関手、導来完備化、実際の零次ホモロジーの関手を合成する。

## 規約
この関手は各項への操作である。複体全体の導来底変換との交換は主張しない。
項の離散性と実際の完備テンソルとの同定は、適用する側で証明する。

## 使われ方
BS 著者版 Theorem 6.4 の古典的な枠の鎖ホモトピーを係数変更後へ移す。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (a : R)

/-- 加群を零次数に置き、主完備化の実際の H⁰ を取る加法的な関手。 -/
def moduleCompletionH0Functor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  moduleObjectFunctor R ⋙ derivedComplexCompletionFunctor R a ⋙
    DerivedCategory.homologyFunctor (ModuleCat R) 0

instance : (moduleCompletionH0Functor R a).Additive := by
  dsimp [moduleCompletionH0Functor]
  infer_instance

/-- H⁰ 主完備化への標準の単位。 -/
def moduleCompletionH0Unit : 𝟭 (ModuleCat.{u} R) ⟶ moduleCompletionH0Functor R a :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (moduleObjectFunctor R) (derivedComplexCompletionUnit R a))
      (DerivedCategory.homologyFunctor (ModuleCat R) 0)

/-- H⁰ 主完備化は導来完備な加群を値に取る。 -/
theorem moduleCompletionH0Functor_isComplete (M : ModuleCat.{u} R) :
    IsModuleComplete R a ((moduleCompletionH0Functor R a).obj M) :=
  derivedComplexCompletionFunctor_homology_isModuleComplete R a ((moduleObjectFunctor R).obj M) 0

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- 通常の係数拡大の後、各加群の H⁰ 主完備化を取る。 -/
def pointwiseCompletedBaseChangeFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  ModuleCat.extendScalars φ ⋙ moduleCompletionH0Functor S (φ a)

instance : (pointwiseCompletedBaseChangeFunctor a φ).Additive := by
  dsimp [pointwiseCompletedBaseChangeFunctor]
  infer_instance

/-- 各項の完備係数拡大は、もとの古典的な鎖ホモトピーを保つ。 -/
def pointwiseCompletedBaseChangeHomotopy
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (((pointwiseCompletedBaseChangeFunctor a φ).mapHomologicalComplex (.up ℕ)).map f)
      (((pointwiseCompletedBaseChangeFunctor a φ).mapHomologicalComplex (.up ℕ)).map g) :=
  (pointwiseCompletedBaseChangeFunctor a φ).mapHomotopy h

end SerrePositivity.DerivedCompletion
