module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces

/-! # Actual face and degeneracy operators on the fixed-object source -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceOperators
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable (C : Type u) [Category.{v} C]

lemma diagram_face {n : ℕ} (i : Fin (n + 2)) :
    (diagram C).δ i = faceHom (D C) (n + 1) i.rev := by
  apply (cancel_mono (comparison C (Opposite.op (SimplexCategory.mk n)))).mp
  change (comparison C (Opposite.op (SimplexCategory.mk (n + 1))) ≫
      (OrdinaryBarFreeResolutionNaturalChoice.source (C := C)).δ i ≫
        inv (comparison C (Opposite.op (SimplexCategory.mk n)))) ≫ _ = _
  rw [OrdinaryBarFreeResolutionNaturalChoice.source_face]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (face_comparison (D C) (n + 1) i.rev).symm

lemma diagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (diagram C).σ i = (degeneracyFunctor (D C) n i.rev).toCatHom := by
  apply (cancel_mono (comparison C (Opposite.op (SimplexCategory.mk (n + 1))))).mp
  change (comparison C (Opposite.op (SimplexCategory.mk n)) ≫
      (OrdinaryBarFreeResolutionNaturalChoice.source (C := C)).σ i ≫
        inv (comparison C (Opposite.op (SimplexCategory.mk (n + 1))))) ≫ _ = _
  rw [OrdinaryBarFreeResolutionNaturalChoice.source_degeneracy]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (degeneracy_comparison (D C) n i.rev).symm

lemma literal_face {n : ℕ} (i : Fin (n + 2)) :
    literalMap C (SimplexCategory.δ i).op = reverseFace (D C) (n + 1) i := by
  rw [literalMap_eq]
  exact congrArg Cat.Hom.toFunctor (diagram_face C i)

lemma literal_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    literalMap C (SimplexCategory.σ i).op = degeneracyFunctor (D C) n i.rev := by
  rw [literalMap_eq]
  exact congrArg Cat.Hom.toFunctor (diagram_degeneracy C i)

abbrev forwardHom (X Y : D C) : SSet.{max u v} :=
  SimplexCategory.rev.op ⋙ OrdinaryBarSourceHom.hom C X Y

lemma forward_face {n : ℕ} (i : Fin (n + 2)) :
    literalMap C (SimplexCategory.rev.map (SimplexCategory.δ i)).op =
      faceFunctor (D C) (n + 1) i := by
  rw [SimplexCategory.rev_map_δ, literal_face]
  simp only [reverseFace, Fin.rev_rev]

lemma forward_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    literalMap C (SimplexCategory.rev.map (SimplexCategory.σ i)).op =
      degeneracyFunctor (D C) n i := by
  rw [SimplexCategory.rev_map_σ, literal_degeneracy, Fin.rev_rev]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceOperators
