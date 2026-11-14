module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0
public import Mathlib.RingTheory.Flat.Equalizer

/-!
概要：適合する切断の部分代数と flat なテンソル積を、最初の余境界の核で比較する。
方針：等化部分代数の加群を核に同定し、tensorKerEquiv を使う。
規約：同型は純テンソルの実際の成分を保つ。
使われ方：局所化後のスカラー写像と次数零の余核の照合。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TensorProduct
open scoped TensorProduct
universe u v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
variable {ι : Type v} [DecidableEq ι] (D : Finset ι ⥤ CommAlgCat.{u} R)

/-- 切断部分代数の flat テンソル積と、テンソル化した余境界の核の同型。 -/
def fullAlgebraCechTensorKernelEquiv :
    A ⊗[R] (fullAlgebraCechEqualizer D) ≃ₗ[A]
      LinearMap.ker (AlgebraTensorModule.lTensor A A
        (fullCechDifferential (algebraCechModuleDiagram D) 1)) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (LinearEquiv.ofEq _ _ (fullAlgebraCechEqualizer_toSubmodule D))).trans
      (LinearMap.tensorKerEquiv A A (fullCechDifferential (algebraCechModuleDiagram D) 1))

/-- 核の比較は、切断の純テンソルを同じ成分の純テンソルへ送る。 -/
theorem fullAlgebraCechTensorKernelEquiv_tmul (a : A) (x : fullAlgebraCechEqualizer D) :
    (fullAlgebraCechTensorKernelEquiv D (a ⊗ₜ[R] x)).val = a ⊗ₜ[R] x.val := by
  rfl

end SerrePositivity.AlgebraicGeometry
