module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraTensorKernel
public import SerrePositivity.AlgebraicGeometry.LinearKernelSquareEquiv

/-!
概要：余境界と可換な各項の底変換同型から、切断部分代数の flat 比較を作る。
方針：テンソル化した核、各項の同型、切断部分代数の核表示を合成する。
規約：ここでは各項の比較を入力し、スキームの底変換での供給は別に行う。
使われ方：実際のスカラーと可換な次数零の底変換比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TensorProduct
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
variable {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (E : Finset ι ⥤ CommAlgCat.{u} A)
variable (e₀ : A ⊗[R] FullCechCochains (algebraCechModuleDiagram D) 1 ≃ₗ[A]
  FullCechCochains (algebraCechModuleDiagram E) 1)
variable (e₁ : A ⊗[R] FullCechCochains (algebraCechModuleDiagram D) 2 ≃ₗ[A]
  FullCechCochains (algebraCechModuleDiagram E) 2)
variable (h : ∀ x, fullCechDifferential (algebraCechModuleDiagram E) 1 (e₀ x) =
  e₁ (AlgebraTensorModule.lTensor A A (fullCechDifferential (algebraCechModuleDiagram D) 1) x))

/-- 各項の flat 底変換比較を適合する切断部分代数へ制限した線形同型。 -/
def fullAlgebraCechTensorComparison :
    A ⊗[R] (fullAlgebraCechEqualizer D) ≃ₗ[A] fullAlgebraCechEqualizer E :=
  (fullAlgebraCechTensorKernelEquiv D).trans
    ((linearKernelEquivOfCommute _ _ e₀ e₁ h).trans
      (LinearEquiv.ofEq _ _ (fullAlgebraCechEqualizer_toSubmodule E)).symm)

/-- 部分代数の底変換比較は、純テンソルに各項の比較を適用したもの。 -/
theorem fullAlgebraCechTensorComparison_tmul (a : A) (x : fullAlgebraCechEqualizer D) :
    (fullAlgebraCechTensorComparison D E e₀ e₁ h (a ⊗ₜ[R] x)).val =
      e₀ (a ⊗ₜ[R] x.val) := rfl

end SerrePositivity.AlgebraicGeometry
