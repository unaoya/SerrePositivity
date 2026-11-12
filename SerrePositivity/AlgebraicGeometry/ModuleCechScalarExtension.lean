module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
概要：スカラーを変える係数の自然な射を、テンソル積からの自然な射へ移す。
方針：加群のスカラー拡大と制限の随伴を、図式圏で使う。
規約：空交叉でも射は定義し、そこで同型とは仮定しない。
使われ方：実際の構造層の引き戻しから Čech の底変換の射を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R A : Type u} [CommRing R] [CommRing A] (α : R →+* A)
variable {C : Type v} [Category C]
variable {D : C ⥤ ModuleCat.{u} R} {E : C ⥤ ModuleCat.{u} A}

/-- スカラーを制限した係数への射の、図式に自然なテンソル積からの延長。 -/
def moduleCechScalarExtension (η : D ⟶ E ⋙ ModuleCat.restrictScalars α) :
    D ⋙ ModuleCat.extendScalars α ⟶ E :=
  (((ModuleCat.extendRestrictScalarsAdj α).whiskerRight C).homEquiv D E).symm η

/-- 自然なテンソル積からの射は、1 と元の切断の純テンソルを引き戻す。 -/
theorem moduleCechScalarExtension_one_tmul
    (η : D ⟶ E ⋙ ModuleCat.restrictScalars α) (c : C) (x : D.obj c) :
    (moduleCechScalarExtension α η).app c
      ((ModuleCat.extendRestrictScalarsAdj α).unit.app (D.obj c) x) = η.app c x := by
  have h := congrArg (fun ζ : D ⟶ E ⋙ ModuleCat.restrictScalars α ↦ ζ.app c x)
    ((((ModuleCat.extendRestrictScalarsAdj α).whiskerRight C).homEquiv D E).apply_symm_apply η)
  exact h

end SerrePositivity.AlgebraicGeometry
