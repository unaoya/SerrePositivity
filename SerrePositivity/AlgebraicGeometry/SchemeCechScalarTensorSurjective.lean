module

public import SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorScalar
public import SerrePositivity.AlgebraicGeometry.AffineIsoSectionAlgebraScalar

/-!
概要：同型になる底変換では、切断部分代数のスカラー写像のテンソル化は全射。
方針：底変換後のスカラー全射性を、実際の同型とスカラーの可換性で戻す。
規約：比較同型や余核の消滅を追加の仮定に置かない。
使われ方：中心外の素点で次数零の余核の台を判定する。
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
variable {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))


include H hU in
/-- 構造射が同型になる flat 底変換では、元のスカラー写像のテンソル化は全射。 -/
theorem schemeCechScalarTensor_surjective [Module.Flat R A] [IsIso iY]
    (hV : ∀ i, IsAffineOpen (g ⁻¹ᵁ U i)) (hcV : (⨆ i, g ⁻¹ᵁ U i) = ⊤) :
    Function.Surjective (AlgebraTensorModule.lTensor A A
      (Algebra.linearMap R (fullAlgebraCechEqualizer
        (schemeSectionAlgebraCechDiagram X (schemeScalarHom X iX) U)))) := by
  intro z
  let e := schemeAlgebraCechTensorEquiv iX iY g H U hU
  obtain ⟨a, ha⟩ := schemeSectionAlgebra_scalar_surjective_of_isIso Y iY
    (fun i ↦ g ⁻¹ᵁ U i) hV hcV (e z)
  refine ⟨a ⊗ₜ[R] (1 : R), e.injective ?_⟩
  change e (a ⊗ₜ[R] (algebraMap R _ 1)) = e z
  rw [map_one]
  exact (schemeAlgebraCechTensorEquiv_scalar iX iY g H U hU a).trans ha

end SerrePositivity.AlgebraicGeometry
