module

public import SerrePositivity.PerfectComplex.Tensor

/-! # Chain maps from a two-term scalar complex specified by two generators -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (l u : ℤ)
variable (eL : P.X l ≅ ModuleCat.of R R) (eU : P.X u ≅ ModuleCat.of R R)
variable (fL : ModuleCat.of R R ⟶ Q.X l) (fU : ModuleCat.of R R ⟶ Q.X u)

def cochainTwoTermScalarMapX (n : ℤ) : P.X n ⟶ Q.X n :=
  if h : n = l then (P.XIsoOfEq h).hom ≫ eL.hom ≫ fL ≫ (Q.XIsoOfEq h).inv
  else if h : n = u then (P.XIsoOfEq h).hom ≫ eU.hom ≫ fU ≫ (Q.XIsoOfEq h).inv
  else 0

@[simp]
lemma cochainTwoTermScalarMapX_lower :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU l = eL.hom ≫ fL := by
  simp [cochainTwoTermScalarMapX]

@[simp]
lemma cochainTwoTermScalarMapX_upper (hne : u ≠ l) :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU u = eU.hom ≫ fU := by
  simp [cochainTwoTermScalarMapX, hne]

variable (hlu : l + 1 = u) (hp : ∀ n, n ≠ l ∧ n ≠ u → IsZero (P.X n)) (r : R)
variable (hd : eL.inv ≫ P.d l u = r • eU.inv)
variable (hL : fL ≫ Q.d l u = r • fU) (hU : fU ≫ Q.d u (u + 1) = 0)

include hlu hp hd hL hU in
lemma cochainTwoTermScalarMapX_comm (n m : ℤ) (h : n + 1 = m) :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU n ≫ Q.d n m =
      P.d n m ≫ cochainTwoTermScalarMapX P Q l u eL eU fL fU m := by
  subst m
  by_cases hnL : n = l
  · subst n
    rw [hlu]
    apply (cancel_epi eL.inv).mp
    simp only [cochainTwoTermScalarMapX_lower,
      cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [hL, ← Category.assoc eL.inv, hd, Linear.smul_comp, Iso.inv_hom_id_assoc]
  · by_cases hnU : n = u
    · subst n
      have hdU : P.d u (u + 1) = 0 := (hp (u + 1) (by omega)).eq_of_tgt _ _
      rw [hdU, zero_comp, cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
        Category.assoc, hU, comp_zero]
    · exact (hp n ⟨hnL, hnU⟩).eq_of_src _ _

def cochainTwoTermScalarMap : P ⟶ Q where
  f := cochainTwoTermScalarMapX P Q l u eL eU fL fU
  comm' n m h := cochainTwoTermScalarMapX_comm P Q l u eL eU fL fU hlu hp r hd hL hU n m h

include hlu hp hd hL hU in
lemma cochainTwoTermScalarMap_eigen (τ : Q ⟶ Q) (c : R)
    (hcL : fL ≫ τ.f l = c • fL) (hcU : fU ≫ τ.f u = c • fU) :
    cochainTwoTermScalarMap P Q l u eL eU fL fU hlu hp r hd hL hU ≫ τ =
      c • cochainTwoTermScalarMap P Q l u eL eU fL fU hlu hp r hd hL hU := by
  apply HomologicalComplex.Hom.ext
  funext n
  change cochainTwoTermScalarMapX P Q l u eL eU fL fU n ≫ τ.f n =
    c • cochainTwoTermScalarMapX P Q l u eL eU fL fU n
  by_cases hnL : n = l
  · subst n
    rw [cochainTwoTermScalarMapX_lower, Category.assoc, hcL, Linear.comp_smul]
  · by_cases hnU : n = u
    · subst n
      rw [cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
        Category.assoc, hcU, Linear.comp_smul]
    · exact (hp n ⟨hnL, hnU⟩).eq_of_src _ _

end SerrePositivity
