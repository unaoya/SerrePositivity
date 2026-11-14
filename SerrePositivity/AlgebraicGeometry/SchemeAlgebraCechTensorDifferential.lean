module

public import SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorTerms
public import SerrePositivity.AlgebraicGeometry.CechAlgebraTensorComparison

/-!
概要：実際の代数係数の底変換比較は最初の余境界と可換。
方針：純テンソルで既存の複体の射の可換性に戻す。
規約：スカラー作用を比較した後の、通常のテンソル積で述べる。
使われ方：切断部分代数の flat な底変換同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct
open scoped TensorProduct ChangeOfRings
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [DecidableEq ι] [Fintype ι] (U : ι → X.Opens)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))


omit [Fintype ι] in
private theorem fullCechComplex_d_zero {B : Type u} [CommRing B]
    (D : Finset ι ⥤ ModuleCat.{u} B) :
    (fullCechComplex D).d 0 1 = ModuleCat.ofHom (fullCechDifferential D 1) := by
  change CochainComplex.of.d
    (fun q ↦ ModuleCat.of B (FullCechCochains D (q + 1)))
    (fun q ↦ ModuleCat.ofHom (fullCechDifferential D (q + 1))) 0 (0 + 1) = _
  exact CochainComplex.of_d _ _ 0

/-- 実際の各項の底変換同型は、最初の余境界と可換。 -/
theorem schemeAlgebraCechTensorTermEquiv_differential
    (x : A ⊗[R] FullCechCochains (algebraCechModuleDiagram
      (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U)) 1) :
    fullCechDifferential (algebraCechModuleDiagram
      (schemeSectionAlgebraCechDiagram Y (schemeScalarHom Y iY) (fun i ↦ g ⁻¹ᵁ U i))) 1
        (schemeAlgebraCechTensorTermEquiv iX iY g H U hU 0 x) =
    schemeAlgebraCechTensorTermEquiv iX iY g H U hU 1
      (AlgebraTensorModule.lTensor A A (fullCechDifferential (algebraCechModuleDiagram
        (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U)) 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    have hc := (schemeStructureCechNativeTensorComplexIso iX iY g H U hU).hom.comm 0 1
    simp only [Functor.mapHomologicalComplex_obj_d, fullCechComplex_d_zero] at hc
    have he := congrArg (fun f ↦ f.hom (a ⊗ₜ[R,algebraMap R A] x)) hc
    exact he
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 実際の flat な底変換と、適合する切断部分代数の線形比較。 -/
def schemeAlgebraCechTensorEquiv [Module.Flat R A] :
    A ⊗[R] fullAlgebraCechEqualizer
      (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U) ≃ₗ[A]
    fullAlgebraCechEqualizer
      (schemeSectionAlgebraCechDiagram Y (schemeScalarHom Y iY) (fun i ↦ g ⁻¹ᵁ U i)) :=
  fullAlgebraCechTensorComparison _ _
    (schemeAlgebraCechTensorTermEquiv iX iY g H U hU 0)
    (schemeAlgebraCechTensorTermEquiv iX iY g H U hU 1)
    (schemeAlgebraCechTensorTermEquiv_differential iX iY g H U hU)

end SerrePositivity.AlgebraicGeometry
