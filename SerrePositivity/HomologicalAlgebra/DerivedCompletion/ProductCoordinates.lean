module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ProductHomology

/-! # 複体の直積の微分と差分の成分計算 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 直積の微分は、各段の微分を成分ごとに取る。 -/
theorem complexProductDegreeEquiv_d (i j : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K j ((piObj K).d i j x) n =
      (K n).d i j (complexProductDegreeEquiv R K i x n) := by
  simp only [complexProductDegreeEquiv_apply]
  exact (congrArg (fun g ↦ g.hom x) ((Pi.π K n).comm i j)).symm

/-- 直積の差分は、成分と次の成分の遷移の差。 -/
theorem complexProductDegreeEquiv_difference
    (t : ∀ n, K (n + 1) ⟶ K n) (i : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K i ((complexTowerDifference R K t).f i x) n =
      complexProductDegreeEquiv R K i x n -
        (t n).f i (complexProductDegreeEquiv R K i x (n + 1)) := by
  simp only [complexProductDegreeEquiv_apply]
  exact congrArg (fun g ↦ (g.f i).hom x) (complexTowerDifference_projection R K t n)

end SerrePositivity.DerivedCompletion
