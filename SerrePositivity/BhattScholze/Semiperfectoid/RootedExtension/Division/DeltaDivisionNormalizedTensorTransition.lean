module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedDirectLimitFlat
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # 有限正規化商の標準射の共通係数商上のテンソル単射性 -/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] deltaDivisionFiniteNormalizedBaseAlgebra
local notation "R₀" => (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)

/-- 任意有限段間の標準射は、共通係数商上の任意加群とテンソルしても単射。 -/
theorem deltaDivisionFiniteNormalizedTower_rTensor_injective
    {n m : ℕ} (h : n ≤ m) (N : Type w) [AddCommGroup N] [Module R₀ N] :
    Function.Injective ((deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N) := by
  let C := DeltaDivisionFiniteNormalizedQuotient D d a u n
  let E := DeltaDivisionFiniteNormalizedQuotient D d a u m
  let := deltaDivisionFiniteNormalizedTowerAlgebra D d a u h
  let : IsScalarTower R₀ C E := IsScalarTower.of_algebraMap_eq
    (fun b => (RingHom.congr_fun (deltaDivisionFiniteNormalizedBaseMap_comp D d a u h) b).symm)
  let := deltaDivisionFiniteNormalizedTower_moduleFaithfullyFlat D d a u h
  let t := TensorProduct.mk C E (C ⊗[R₀] N) 1
  have ht : Function.Injective t :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := C) (B := E) (C ⊗[R₀] N)
  let e₁ := (TensorProduct.AlgebraTensorModule.assoc R₀ C C E C N).symm.restrictScalars R₀
  let e₂ := TensorProduct.congr ((TensorProduct.rid C E).restrictScalars R₀) (LinearEquiv.refl R₀ N)
  let e := e₁.trans e₂
  have he : e.toLinearMap.comp (t.restrictScalars R₀) =
      (deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N := by
    apply TensorProduct.ext'
    intro x y
    change e (1 ⊗ₜ[C] (x ⊗ₜ[R₀] y)) =
      (deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) x ⊗ₜ[R₀] y
    simp only [e, e₁, e₂, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      TensorProduct.AlgebraTensorModule.assoc_symm_tmul, TensorProduct.congr_tmul,
      TensorProduct.rid_tmul, LinearEquiv.refl_apply]
    change (algebraMap C E x * 1) ⊗ₜ[R₀] y = _
    rw [mul_one]
    rfl
  have hi : Function.Injective (e.toLinearMap.comp (t.restrictScalars R₀)) := e.injective.comp ht
  rw [he] at hi
  exact hi

end SerrePositivity.BhattScholze
