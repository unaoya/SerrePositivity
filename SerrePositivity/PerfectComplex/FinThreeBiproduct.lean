module

public import SerrePositivity.PerfectComplex.ClosedSupportBiproduct
public import SerrePositivity.PerfectComplex.DegreewiseRetract

/-! # The finite biproduct of three complexes as a binary iterated sum -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

/-- The three ordered projections from the iterated binary sum. -/
def cochainFinThreeProjection (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ) :
    ∀ i : Fin 3, P 0 ⊞ (P 1 ⊞ P 2) ⟶ P i :=
  Fin.cases biprod.fst
    (Fin.cases (biprod.snd ≫ biprod.fst)
      (Fin.cases (biprod.snd ≫ biprod.snd) (fun i => Fin.elim0 i)))

@[simp]
lemma cochainFinThreeProjection_zero (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainFinThreeProjection P 0 = biprod.fst := rfl

@[simp]
lemma cochainFinThreeProjection_one (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainFinThreeProjection P 1 = biprod.snd ≫ biprod.fst := rfl

@[simp]
lemma cochainFinThreeProjection_two (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainFinThreeProjection P 2 = biprod.snd ≫ biprod.snd := rfl

/-- Reexpress the Fin 3 biproduct as a binary sum with the same ordered components. -/
def cochainFinThreeBiproductIso (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ) :
    (⨁ P) ≅ P 0 ⊞ (P 1 ⊞ P 2) where
  hom := biprod.lift (biproduct.π P 0) (biprod.lift (biproduct.π P 1) (biproduct.π P 2))
  inv := biproduct.lift (cochainFinThreeProjection P)
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    fin_cases i <;> fin_cases j <;> simp [Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · simp [Category.assoc]
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]

lemma cochainFinThreeBiproduct_perfect
    (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, strictlyPerfectComplex R (P i)) : strictlyPerfectComplex R (⨁ P) := by
  let e := cochainFinThreeBiproductIso P
  exact strictlyPerfectComplex_of_degreewiseRetract e.hom e.inv.f (fun n => by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f n) e.hom_inv_id)
    (strictlyPerfectComplex_biprod (hp 0) (strictlyPerfectComplex_biprod (hp 1) (hp 2)))

lemma cochainFinThreeBiproduct_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ)
    (hs : ∀ i, HasHomologySupportOn Z (P i)) : HasHomologySupportOn Z (⨁ P) :=
  ((hs 0).biprod ((hs 1).biprod (hs 2))).of_iso (cochainFinThreeBiproductIso P).symm

lemma K0WithSupport.mk_finThreeBiproduct
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P : Fin 3 → CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, strictlyPerfectComplex R (P i)) (hs : ∀ i, HasHomologySupportOn Z (P i)) :
    K0WithSupport.mk Z (supportedPerfectOnObj Z (⨁ P)
      (cochainFinThreeBiproduct_perfect P hp) (cochainFinThreeBiproduct_support P hs)) =
      ∑ i : Fin 3, K0WithSupport.mk Z (supportedPerfectOnObj Z (P i) (hp i) (hs i)) := by
  have h := K0WithSupport.mk_eq_of_quasiIso Z _ _
    (cochainFinThreeBiproduct_perfect P hp)
    (strictlyPerfectComplex_biprod (hp 0) (strictlyPerfectComplex_biprod (hp 1) (hp 2)))
    (cochainFinThreeBiproduct_support P hs) ((hs 0).biprod ((hs 1).biprod (hs 2)))
    (cochainFinThreeBiproductIso P).hom
  rw [h, K0WithSupport.mk_biprod Z (P 0) (P 1 ⊞ P 2) (hp 0)
    (strictlyPerfectComplex_biprod (hp 1) (hp 2)) (hs 0) ((hs 1).biprod (hs 2)),
    K0WithSupport.mk_biprod Z (P 1) (P 2) (hp 1) (hp 2) (hs 1) (hs 2),
    Fin.sum_univ_three, add_assoc]

end SerrePositivity
