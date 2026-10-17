module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DegenerateHornInput
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy

/-! # Two degenerate triangles with the same horn are the same whole triangle

The parameter is arbitrary and the target need not be Kan. All three
possible missing faces are handled, including the middle horn. This
is the overlap compatibility required to prescribe both degeneracies
to one uniform triangle filling operation.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.DegenerateTriangleOverlap
open ComparisonTriangleDegeneracy
abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)
abbrev constant (e : Fin 2) : interval.{v} ⟶ interval :=
  SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ e

private lemma sigma_constant (e : Fin 2) :
    SSet.stdSimplex.σ.{v} (0 : Fin 2) ≫ constant e =
      SSet.stdSimplex.σ (1 : Fin 2) ≫ constant e := by
  change SSet.stdSimplex.map _ ≫ (SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _) =
    SSet.stdSimplex.map _ ≫ (SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _)
  simp only [← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  fin_cases e <;> decide

private lemma constant_end_start : constant.{v} 0 ≫ constant 1 = constant 1 := by
  change (SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _) ≫
    (SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _) =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  simp only [← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable (K : SSet.{v}) (i : Fin 3) {L : SSet.{v}}
  (a b : L ⟶ (ihom interval).obj K)
  (h : a ≫ DegenerateHornInput.boundary i 0 K = b ≫ DegenerateHornInput.boundary i 1 K)

include h in
private lemma face_eq (j : Fin 3) (hj : j ≠ i) :
    a ≫ (pre (SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ (0 : Fin 2))).app K =
      b ≫ (pre (SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ (1 : Fin 2))).app K := by
  let e := SSet.horn.ι i j hj
  have he : KanHornFamilyLifting.restriction K i ≫ (pre e).app K =
      (pre (SSet.stdSimplex.δ j)).app K := by
    have he' : (pre (SSet.horn 2 i).ι).app K ≫ (pre e).app K =
        (pre (e ≫ (SSet.horn 2 i).ι)).app K := RelativeChoiceSpace.restriction_comp _ _
    rw [SSet.horn.ι_ι] at he'
    exact he'
  have h₀ : (pre (SSet.stdSimplex.σ (0 : Fin 2))).app K ≫
      (pre (SSet.stdSimplex.δ j)).app K =
      (pre (SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ (0 : Fin 2))).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  have h₁ : (pre (SSet.stdSimplex.σ (1 : Fin 2))).app K ≫
      (pre (SSet.stdSimplex.δ j)).app K =
      (pre (SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ (1 : Fin 2))).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  have hh := congrArg (fun q => q ≫ (pre e).app K) h
  change (a ≫ (pre (SSet.stdSimplex.σ (0 : Fin 2))).app K ≫
    KanHornFamilyLifting.restriction K i) ≫ (pre e).app K =
    (b ≫ (pre (SSet.stdSimplex.σ (1 : Fin 2))).app K ≫
      KanHornFamilyLifting.restriction K i) ≫ (pre e).app K at hh
  simpa only [Category.assoc, he, h₀, h₁] using hh

include h in
private lemma face_zero (hi : (0 : Fin 3) ≠ i) : a = b ≫ (pre (constant 0)).app K := by
  have hh := face_eq K i a b h 0 hi
  have hc : SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
    face_collapse_zero (0 : Fin 2)
  rw [hc, face_collapse_end, pre_id, NatTrans.id_app, Category.comp_id] at hh
  exact hh

include h in
private lemma face_one (hi : (1 : Fin 3) ≠ i) : a = b := by
  have hh := face_eq K i a b h 1 hi
  have hc₀ : SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
    face_collapse_zero (1 : Fin 2)
  have hc₁ : SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ :=
    face_collapse_one (0 : Fin 2)
  simpa only [hc₀, hc₁, pre_id, NatTrans.id_app, Category.comp_id] using hh

include h in
private lemma face_two (hi : (2 : Fin 3) ≠ i) : a ≫ (pre (constant 1)).app K = b := by
  have hh := face_eq K i a b h 2 hi
  have hc : SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ :=
    face_collapse_one (1 : Fin 2)
  rw [face_collapse_start, hc, pre_id, NatTrans.id_app, Category.comp_id] at hh
  exact hh

private lemma equal_degeneracies (e : Fin 2) (ha : a ≫ (pre (constant e)).app K = a) :
    a ≫ DegenerateHornInput.degeneracy 0 K = a ≫ DegenerateHornInput.degeneracy 1 K := by
  have h₀ : (pre (constant e)).app K ≫ (pre (SSet.stdSimplex.σ (0 : Fin 2))).app K =
      (pre (SSet.stdSimplex.σ (0 : Fin 2) ≫ constant e)).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  have h₁ : (pre (constant e)).app K ≫ (pre (SSet.stdSimplex.σ (1 : Fin 2))).app K =
      (pre (SSet.stdSimplex.σ (1 : Fin 2) ≫ constant e)).app K :=
    RelativeChoiceSpace.restriction_comp _ _
  calc
    _ = (a ≫ (pre (constant e)).app K) ≫ DegenerateHornInput.degeneracy 0 K := by rw [ha]
    _ = a ≫ (pre (SSet.stdSimplex.σ (0 : Fin 2) ≫ constant e)).app K := by
      rw [Category.assoc, h₀]
    _ = a ≫ (pre (SSet.stdSimplex.σ (1 : Fin 2) ≫ constant e)).app K := by
      rw [sigma_constant]
    _ = (a ≫ (pre (constant e)).app K) ≫ DegenerateHornInput.degeneracy 1 K := by
      rw [Category.assoc, h₁]
    _ = _ := by rw [ha]

include h in
lemma eq_of_same_horn : a ≫ DegenerateHornInput.degeneracy 0 K =
    b ≫ DegenerateHornInput.degeneracy 1 K := by
  fin_cases i
  · have hab := face_one K 0 a b h (by decide)
    have hc := (face_two K 0 a b h (by decide)).trans hab.symm
    exact (equal_degeneracies K a 1 hc).trans
      (congrArg (fun q => q ≫ DegenerateHornInput.degeneracy 1 K) hab)
  · have h₀ := face_zero K 1 a b h (by decide)
    have h₂ := face_two K 1 a b h (by decide)
    have hc : (pre (constant 1)).app K ≫ (pre (constant 0)).app K =
        (pre (constant 1)).app K := by
      have he : (pre (constant 1)).app K ≫ (pre (constant 0)).app K =
          (pre (constant 0 ≫ constant 1)).app K := RelativeChoiceSpace.restriction_comp _ _
      rw [constant_end_start] at he
      exact he
    have hab : a = b := calc
      _ = b ≫ (pre (constant 0)).app K := h₀
      _ = (a ≫ (pre (constant 1)).app K) ≫ (pre (constant 0)).app K := by rw [h₂]
      _ = a ≫ (pre (constant 1)).app K := by rw [Category.assoc, hc]
      _ = b := h₂
    exact (equal_degeneracies K a 1 (h₂.trans hab.symm)).trans
      (congrArg (fun q => q ≫ DegenerateHornInput.degeneracy 1 K) hab)
  · have hab := face_one K 2 a b h (by decide)
    have hc : a ≫ (pre (constant 0)).app K = a := by
      rw [hab]
      exact (face_zero K 2 a b h (by decide)).symm.trans hab
    exact (equal_degeneracies K a 0 hc).trans
      (congrArg (fun q => q ≫ DegenerateHornInput.degeneracy 1 K) hab)

end SerrePositivity.SimplicialModel.DegenerateTriangleOverlap
