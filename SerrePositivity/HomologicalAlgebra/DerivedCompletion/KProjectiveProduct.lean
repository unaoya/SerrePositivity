module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # K射影的な始域から見た、導来像の直積射影による検出

各成分で零になる導来射を、K射影性で実際の鎖写像へ戻し、
成分の零ホモトピーをまとめて全体の零性を示す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- K射影的な始域からの導来射は、直積のすべての射影によって零性を検出できる。 -/
theorem Qh_hom_eq_zero_of_product_projections
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (a : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (piObj K)))
    (ha : ∀ n, a ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (Pi.π K n)) = 0) : a = 0 := by
  obtain ⟨b, rfl⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P _).surjective a
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective b
  have hf : ∀ n, Nonempty (Homotopy (f ≫ Pi.π K n) 0) := by
    intro n
    apply (HomotopyCategory.quotient_map_eq_zero_iff _).mp
    apply (CochainComplex.IsKProjective.Qh_map_bijective P _).injective
    simpa only [Functor.map_comp, Functor.map_zero] using ha n
  have hzero := (HomotopyCategory.quotient_map_eq_zero_iff f).mpr
    (complexProduct_nonempty_homotopy_zero R K f hf)
  rw [hzero, Functor.map_zero]

/-- 同じ検出定理を、複体の導来像Qを使う形で述べる。 -/
theorem Q_hom_eq_zero_of_product_projections
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (piObj K))
    (ha : ∀ n, a ≫ DerivedCategory.Q.map (Pi.π K n) = 0) : a = 0 := by
  let e := DerivedCategory.quotientCompQhIso (ModuleCat R)
  have hzero : (e.app P).hom ≫ a ≫ (e.app (piObj K)).inv = 0 := by
    apply Qh_hom_eq_zero_of_product_projections R P K
    intro n
    change ((e.app P).hom ≫ a ≫ (e.app (piObj K)).inv) ≫
      (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map (Pi.π K n) = 0
    simp only [assoc]
    change (e.hom.app P) ≫ a ≫ e.inv.app (piObj K) ≫
      (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map (Pi.π K n) = 0
    rw [← e.inv.naturality, ← assoc a, ha n, zero_comp, comp_zero]
  apply (cancel_mono (e.app (piObj K)).inv).mp
  apply (cancel_epi (e.app P).hom).mp
  simpa only [assoc, zero_comp, comp_zero] using hzero

/-- 全整数次数の導来射も、直積のすべての射影で零性を検出できる。 -/
theorem Q_shiftedHom_eq_zero_of_product_projections
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (a : ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj (piObj K)) m)
    (ha : ∀ n, a ≫ (DerivedCategory.Q.map (Pi.π K n))⟦m⟧' = 0) : a = 0 := by
  let C := ConcreteDerivedCategory R
  let e := shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)
  let s := (DerivedCategory.Q.commShiftIso (-m)).hom.app P
  have hzero : s ≫ a⟦-m⟧' ≫ e.hom.app (DerivedCategory.Q.obj (piObj K)) = 0 := by
    apply Q_hom_eq_zero_of_product_projections R (P⟦-m⟧) K
    intro n
    simp only [assoc]
    change s ≫ a⟦-m⟧' ≫ e.hom.app (DerivedCategory.Q.obj (piObj K)) ≫
      (𝟭 C).map (DerivedCategory.Q.map (Pi.π K n)) = 0
    rw [← e.hom.naturality]
    change s ≫ a⟦-m⟧' ≫ (DerivedCategory.Q.map (Pi.π K n))⟦m⟧'⟦-m⟧' ≫
      e.hom.app (DerivedCategory.Q.obj (K n)) = 0
    rw [← assoc (a⟦-m⟧'), ← Functor.map_comp, ha n, Functor.map_zero, zero_comp, comp_zero]
  have hmap : a⟦-m⟧' = 0 := by
    apply (cancel_epi s).mp
    apply (cancel_mono (e.hom.app (DerivedCategory.Q.obj (piObj K)))).mp
    simpa only [assoc, zero_comp, comp_zero] using hzero
  apply (shiftFunctor C (-m)).map_injective
  simpa only [Functor.map_zero] using hmap

end SerrePositivity.DerivedCompletion
