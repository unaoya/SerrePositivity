module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompleteness
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-!
# 元の導来係数拡大とスカラーによる零化

## 概要
元のスカラー倍の像と、係数拡大先のそのスカラーの像による倍写像を比較する。

## 方針
指定された射影模型の持ち上げを元のスカラー倍へホモトピーで比較し、元の係数拡大で写す。

## 規約
環射の平坦性を仮定しない。完備化前の実際の導来底変換に適用する。

## 使われ方
生成元で零化された元の剰余行の底変換の導来完備性。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B]

/-- 元の導来底変換はスカラー倍を、その像によるスカラー倍へ移す。 -/
theorem derivedBaseChange_scalar_id (φ : R →+* B) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedBaseChange φ).map (a • 𝟙 X)).hom =
      φ a • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X).obj := by
  let P := boundedAboveDerivedChosenModel X
  have h : Homotopy (P.map P (a • 𝟙 X.obj)) (SerrePositivity.smulId a P.complex) := by
    apply P.mapHomotopyOfNaturality P
    simp [SerrePositivity.smulId, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
  change DerivedCategory.Q.map
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      (P.map P (a • 𝟙 X.obj))) = _
  rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat B)
    ((ModuleCat.extendScalars φ).mapHomotopy h), SerrePositivity.baseChange_smulId]
  simp only [SerrePositivity.smulId, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- 元の対象を零化するスカラーの像も、実際の導来底変換の対象を零化する。 -/
theorem derivedBaseChange_scalar_zero (φ : R →+* B) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (ha : a • 𝟙 X = 0) :
    φ a • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X).obj = 0 := by
  haveI : (boundedAboveDerivedBaseChange φ).Additive := by
    change (boundedAboveLeftDerived (ModuleCat.extendScalars φ)).Additive
    infer_instance
  have h := congrArg (fun f => ((boundedAboveDerivedBaseChange φ).map f).hom) ha
  rw [derivedBaseChange_scalar_id, Functor.map_zero] at h
  change φ a • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X).obj =
    DerivedCategory.Minus.ι.map
      (0 : (boundedAboveDerivedBaseChange φ).obj X ⟶ (boundedAboveDerivedBaseChange φ).obj X) at h
  simpa only [Functor.map_zero] using h

/-- 元の対象を零化するスカラーの像について、その導来底変換は完備である。 -/
theorem derivedBaseChange_complete_of_scalar_zero (φ : R →+* B) (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (ha : a • 𝟙 X = 0) :
    IsComplete B (φ a) ((boundedAboveDerivedBaseChange φ).obj X).obj := by
  apply isComplete_of_scalar_pow_zero B (φ a) _ 1
  simpa only [pow_one] using derivedBaseChange_scalar_zero φ a X ha

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
