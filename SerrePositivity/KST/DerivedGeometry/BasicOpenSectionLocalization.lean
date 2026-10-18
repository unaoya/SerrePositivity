module

public import SerrePositivity.KST.DerivedGeometry.IteratedAwayLocalization
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
概要：tilde 層の D(b) から D(ab) への制限は a の局所化。
方針：大域切断からの二つの局所化と反復局所化の定理を使う。
規約：切断の加群構造は modulesSpecToSheaf による実際の R 加群構造。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/--
概要：tilde 層の基本開の包含 D(ab) ⊆ D(b) による制限は a の局所化。
方針：M からの b と ab の局所化を制限の合成恒等式で比較する。
規約：基本開の切断は既存の tilde の切断そのもの。
使われ方：TT §3、Toën §3.2 の Čech 各項の局所化比較。
-/
theorem tilde_basicOpenRestriction_isLocalized (a b : R) :
    IsLocalizedModule.Away a
      (((modulesSpecToSheaf.obj (tilde M)).obj.map
        (homOfLE (basicOpen_mul_le_right a b)).op).hom) := by
  let f := (tilde.toOpen M (basicOpen b)).hom
  let g := ((modulesSpecToSheaf.obj (tilde M)).obj.map
    (homOfLE (basicOpen_mul_le_right a b)).op).hom
  have hcomp : g ∘ₗ f = (tilde.toOpen M (basicOpen (a * b))).hom :=
    congrArg ModuleCat.Hom.hom (tilde.toOpen_res M (basicOpen b) (basicOpen (a * b))
      (homOfLE (basicOpen_mul_le_right a b)))
  have hi : IsLocalizedModule (.powers (a * b))
      (tilde.toOpen M (basicOpen (a * b))).hom := inferInstance
  have : IsLocalizedModule.Away (a * b) (g ∘ₗ f) := hcomp.symm ▸ hi
  exact awayLocalization_of_composite a b f g

end SerrePositivity.KST.DerivedGeometry
