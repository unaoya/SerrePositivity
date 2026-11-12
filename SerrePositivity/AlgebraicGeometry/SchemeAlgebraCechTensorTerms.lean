module

public import SerrePositivity.AlgebraicGeometry.TensorExtendScalarsEquiv
public import SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechNativeTensor
public import SerrePositivity.AlgebraicGeometry.CechCoefficientExactness

/-!
概要：実際の底変換の各 Čech 項を、代数係数のテンソル積として比較する。
方針：代数係数と構造層係数を両端で比較し、既存の複体の同型を使う。
規約：増大項を含まない正の長さのタプルに適用する。
使われ方：切断部分代数の flat 比較へ実際の各項の同型を供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [DecidableEq ι] [Fintype ι] (U : ι → X.Opens)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))

/-- 実際の底変換の代数係数の各 Čech 項と、通常のテンソル積の比較。 -/
def schemeAlgebraCechTensorTermEquiv (q : ℕ) :
    A ⊗[R] FullCechCochains (algebraCechModuleDiagram
      (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U)) (q + 1) ≃ₗ[A]
      FullCechCochains (algebraCechModuleDiagram
        (schemeSectionAlgebraCechDiagram Y (schemeScalarHom Y iY) (fun i ↦ g ⁻¹ᵁ U i))) (q + 1) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (fullCechCoefficientEquiv (schemeSectionAlgebraCechModuleIso X (schemeScalarHom X iX) U)
      (q + 1))).trans
    ((tensorExtendScalarsEquiv _).trans
      ((((HomologicalComplex.eval (ModuleCat A) (.up ℕ) q).mapIso
        (schemeStructureCechNativeTensorComplexIso iX iY g H U hU)).toLinearEquiv).trans
        (fullCechCoefficientEquiv
          (schemeSectionAlgebraCechModuleIso Y (schemeScalarHom Y iY) (fun i ↦ g ⁻¹ᵁ U i)).symm
          (q + 1))))

end SerrePositivity.AlgebraicGeometry
