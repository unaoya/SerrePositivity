module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-! # Fibrant fibrations detect the weak-equivalence part of a lifting class

A map lifting against every fibration between fibrant objects is a weak
equivalence. Fibrant replacements and one very good path object provide
an inverse in the ordinary localization. No cofibrancy, properness,
smallness or functorial factorization is required.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]

lemma weakEquivalence_of_lifts_fibrant_fibrations {A B : C} (j : A ⟶ B)
    (h : ∀ {X Y : C} (p : X ⟶ Y), IsFibrant X → IsFibrant Y →
      Fibration p → HasLiftingProperty j p) : weakEquivalences C j := by
  let x := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from A)
  let y := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from B)
  have : Fibration x.p := ⟨x.hp⟩
  have : Fibration y.p := ⟨y.hp⟩
  have : IsFibrant x.Z := (isFibrant_iff_of_isTerminal x.p terminalIsTerminal).mpr inferInstance
  have : IsFibrant y.Z := (isFibrant_iff_of_isTerminal y.p terminalIsTerminal).mpr inferInstance
  have : IsFibrant (⊤_ C) := by
    change Fibration (terminal.from (⊤_ C))
    rw [show terminal.from (⊤_ C) = 𝟙 (⊤_ C) from terminal.hom_ext _ _]
    infer_instance
  have : HasLiftingProperty j (terminal.from x.Z) := h _ inferInstance inferInstance inferInstance
  have sa : CommSq x.i j (terminal.from x.Z) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  let a := sa.lift
  have ha : j ≫ a = x.i := sa.fac_left
  have : Cofibration x.i := ⟨x.hi.1⟩
  have : WeakEquivalence x.i := ⟨x.hi.2⟩
  have sg : CommSq (j ≫ y.i) x.i (terminal.from y.Z) (terminal.from x.Z) :=
    ⟨terminal.hom_ext _ _⟩
  let g := sg.lift
  have hg : x.i ≫ g = j ≫ y.i := sg.fac_left
  obtain ⟨P, hP⟩ := PathObject.exists_very_good y.Z
  have := hP
  have : IsFibrant (y.Z ⨯ y.Z) := isFibrant_of_fibration (prod.fst : y.Z ⨯ y.Z ⟶ y.Z)
  have : HasLiftingProperty j P.p := h _ inferInstance inferInstance inferInstance
  have sp : CommSq ((j ≫ y.i) ≫ P.ι) j P.p (prod.lift (a ≫ g) y.i) := by
    constructor
    apply prod.hom_ext
    · simp only [Category.assoc, PrepathObject.p_fst, PrepathObject.ι_p₀,
        Category.comp_id, prod.lift_fst]
      exact hg.symm.trans (by rw [← ha, Category.assoc])
    · simp only [Category.assoc, PrepathObject.p_snd, PrepathObject.ι_p₁,
        Category.comp_id, prod.lift_snd]
  let Q := (weakEquivalences C).Q
  have : IsIso (Q.map x.i) := Localization.inverts Q (weakEquivalences C) _ x.hi.2
  have : IsIso (Q.map y.i) := Localization.inverts Q (weakEquivalences C) _ y.hi.2
  have : IsIso (Q.map P.ι) := Localization.inverts Q (weakEquivalences C) _
    (mem_weakEquivalences P.ι)
  have hp : Q.map P.p₀ = Q.map P.p₁ := by
    apply (cancel_epi (Q.map P.ι)).mp
    simp only [← Q.map_comp, PrepathObject.ι_p₀, PrepathObject.ι_p₁]
  have he : Q.map (a ≫ g) = Q.map y.i := by
    have he₀ : sp.lift ≫ P.p₀ = a ≫ g := by
      simp only [← PrepathObject.p_fst, ← Category.assoc, sp.fac_right, prod.lift_fst]
    have he₁ : sp.lift ≫ P.p₁ = y.i := by
      simp only [← PrepathObject.p_snd, ← Category.assoc, sp.fac_right, prod.lift_snd]
    rw [← he₀, Q.map_comp, hp, ← Q.map_comp, he₁]
  let r := Q.map a ≫ inv (Q.map x.i)
  have hjr : Q.map j ≫ r = 𝟙 _ := by
    dsimp [r]
    rw [← Category.assoc, ← Q.map_comp, ha, IsIso.hom_inv_id]
  have hrj : r ≫ Q.map j = 𝟙 _ := by
    have hxg : Q.map x.i ≫ Q.map g = Q.map j ≫ Q.map y.i := by
      rw [← Q.map_comp, hg, Q.map_comp]
    have hxj : inv (Q.map x.i) ≫ Q.map j = Q.map g ≫ inv (Q.map y.i) := by
      apply (cancel_mono (Q.map y.i)).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← hxg, IsIso.inv_hom_id_assoc]
    dsimp [r]
    rw [Category.assoc, hxj, ← Category.assoc, ← Q.map_comp, he, IsIso.hom_inv_id]
  have : IsIso (Q.map j) := ⟨r, hjr, hrj⟩
  exact (weakEquivalences_iff_isIso_map Q j).mpr inferInstance

end SerrePositivity.Quillen
