module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraAugmentation

/-!
概要：増大 Čech の左端の単射性を、実際の代数の増大へ戻す。
方針：空タプルの同型と次数零の微分との一致を使う。
規約：単射性は元の増大写像について述べる。
使われ方：アフィン被覆での大域切断と適合する切断の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R)

/-- Čech の左端が単射なら、実際の代数の増大も単射。 -/
theorem fullAlgebraCechAugmentation_injective_of_differential
    (h : Function.Injective (fullCechDifferential (algebraCechModuleDiagram D) 0)) :
    Function.Injective (fullAlgebraCechAugmentation D) := by
  intro x y hxy
  apply (fullCechZeroCochainsEquiv (algebraCechModuleDiagram D)).symm.injective
  apply h
  have hx := LinearMap.congr_fun (fullAlgebraCechAugmentation_eq_differential D) x
  have hy := LinearMap.congr_fun (fullAlgebraCechAugmentation_eq_differential D) y
  exact hx.symm.trans ((congrArg Subtype.val hxy).trans hy)

end SerrePositivity.AlgebraicGeometry
