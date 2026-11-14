module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeTensor

/-!
概要：アフィン底変換の切断の環同型を、純テンソルの式と線形同型へ移す。
方針：pushout の左右の入射の式と、テンソル積の乗法を使う。
規約：構造射の定める scalar action を、束ねた CommAlgCat の値として明示する。
使われ方：Čech 複体の底変換と閉厚化の実際の係数の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A)) (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable (U : X.Opens) (hU : IsAffineOpen U)

/-- 純テンソルの実際の切断への像は、scalar の像と切断の引き戻しの積。 -/
theorem schemeAffineBaseChangeTensorIso_tmul (a : A) (x : schemeAffineSectionAlgebra iX U) :
    (schemeAffineBaseChangeTensorIso iX iY g H U hU).hom.hom (a ⊗ₜ[R] x) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ iY.appLE ⊤ (g ⁻¹ᵁ U) (by simp)).hom a) *
        ((g.appLE U (g ⁻¹ᵁ U) le_rfl).hom x) := by
  have hleft := congrArg (fun f : CommRingCat.of A ⟶ Γ(Y, g ⁻¹ᵁ U) ↦ f.hom a)
    (schemeAffineBaseChangeTensorIso_left iX iY g H U hU)
  have hright := congrArg (fun f : CommRingCat.of (schemeAffineSectionAlgebra iX U) ⟶
      Γ(Y, g ⁻¹ᵁ U) ↦ f.hom x)
    (schemeAffineBaseChangeTensorIso_right iX iY g H U hU)
  have hprod : a ⊗ₜ[R] x =
      (Algebra.TensorProduct.includeLeftRingHom a) *
        (Algebra.TensorProduct.includeRight.toRingHom x) := by
    change a ⊗ₜ[R] x = (a ⊗ₜ[R] (1 : schemeAffineSectionAlgebra iX U)) * ((1 : A) ⊗ₜ[R] x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hprod, map_mul]
  exact congrArg₂ (fun a b : Γ(Y, g ⁻¹ᵁ U) ↦ a * b) hleft hright

/-- 実際のアフィン底変換の切断の比較は、底変換先の環上で線形。 -/
def schemeAffineBaseChangeSectionsLinearEquiv :
    A ⊗[R] (schemeAffineSectionAlgebra iX U) ≃ₗ[A]
      (schemeAffineSectionAlgebra iY (g ⁻¹ᵁ U)) := by
  let e : (A ⊗[R] (schemeAffineSectionAlgebra iX U)) ≃+*
      (schemeAffineSectionAlgebra iY (g ⁻¹ᵁ U)) :=
    (schemeAffineBaseChangeTensorIso iX iY g H U hU).commRingCatIsoToRingEquiv
  let eA : (A ⊗[R] (schemeAffineSectionAlgebra iX U)) ≃ₐ[A]
      (schemeAffineSectionAlgebra iY (g ⁻¹ᵁ U)) :=
    { e with
      commutes' := by
        intro a
        exact congrArg (fun f : CommRingCat.of A ⟶ Γ(Y, g ⁻¹ᵁ U) ↦ f.hom a)
          (schemeAffineBaseChangeTensorIso_left iX iY g H U hU) }
  exact eA.toLinearEquiv

end SerrePositivity.AlgebraicGeometry
