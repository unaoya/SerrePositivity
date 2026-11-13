module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntRestriction
public import Mathlib.Algebra.Ring.ULift

/-!
概要：整数加群の係数図式を同じ宇宙の ULift ℤ の加群へ移す。
方針：環同型に沿う係数制限と、既存の整数係数の Čech 比較を使う。
規約：加群の台集合を縮小しない。
使われ方：2e の filtered 余極限の比較を任意の宇宙の整数加群へ適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ ModuleCat.{u} ℤ)

/-- 整数係数の同じ加群を ULift ℤ の加群として扱う。 -/
abbrev projectiveIntCechLiftDiagram : Finset ι ⥤ ModuleCat.{u} (ULift.{u} ℤ) :=
  D ⋙ ModuleCat.restrictScalars (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ)

/-- ULift ℤ への移送を整数へ戻すと、元の係数図式になる。 -/
def projectiveIntCechLiftRoundtripIso :
    projectiveIntCechLiftDiagram D ⋙
        ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ)) ≅ D :=
  NatIso.ofComponents
    (fun T ↦ LinearEquiv.toModuleIso
      (show ((projectiveIntCechLiftDiagram D ⋙
        ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))).obj T) ≃ₗ[ℤ]
        D.obj T from (AddEquiv.refl (D.obj T)).toIntLinearEquiv))
    (by intro T U h; ext x; rfl)

/-- ULift ℤ に移した Čech H と元の整数係数の Čech H の同型。
BST13 Lemma 3.9 の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
def projectiveIntCechLiftHomologyIso (q : ℕ) :
    (fullCechComplex D).homology q ≅
      (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))).obj
        ((fullCechComplex (projectiveIntCechLiftDiagram D)).homology q) :=
  (fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).mapIso
      (projectiveIntCechLiftRoundtripIso D).symm ≪≫
    projectiveCechIntRestrictionHomologyIso (projectiveIntCechLiftDiagram D) q

end SerrePositivity.AlgebraicGeometry
