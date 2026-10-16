import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution

universe v u
noncomputable section
open CategoryTheory SimplexCategoryGenRel
open SerrePositivity
open SerrePositivity.HomotopyFunctionComplex

-- The comparison is proved on arbitrary morphisms, including mixed face/degeneracy words.
example : toSimplexCategory.Faithful := inferInstance
example : toSimplexCategory.Full := inferInstance
example : toSimplexCategory.IsEquivalence := inferInstance
example : SimplexCategoryGenRel ≌ SimplexCategory := SimplexPresentation.equivalence

example {x y : SimplexCategoryGenRel} (f g : x ⟶ y)
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g :=
  SimplexPresentation.toSimplexCategory_map_injective f g h

example {x y : SimplexCategoryGenRel} (f : toSimplexCategory.obj x ⟶ toSimplexCategory.obj y) :
    ∃ g : x ⟶ y, toSimplexCategory.map g = f := toSimplexCategory.map_surjective f

example : SimplexPresentation.inverse ⋙ toSimplexCategory = 𝟭 _ :=
  SimplexPresentation.inverse_toSimplexCategory
example : toSimplexCategory ⋙ SimplexPresentation.inverse = 𝟭 _ :=
  SimplexPresentation.toSimplexCategory_inverse

example {n : ℕ} (i : Fin (n + 2)) :
    SimplexPresentation.inverse.map (SimplexCategory.δ i) = δ i :=
  SimplexPresentation.inverse_face i
example {n : ℕ} (i : Fin (n + 1)) :
    SimplexPresentation.inverse.map (SimplexCategory.σ i) = σ i :=
  SimplexPresentation.inverse_degeneracy i

-- The missing-vertex description holds in every degree, not just low-dimensional examples.
example (L : List ℕ) {m n : ℕ} (h : m + L.length = n)
    (hL : IsAdmissible (m + 1) L) (k : Fin (n + 1)) :
    (∃ j, (toSimplexCategory.map (SimplexPresentation.standardδ L h)).toOrderHom j = k) ↔
      k.val ∉ L := SimplexPresentation.standardδ_range L h hL k

section Comonad
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)

example : SimplicialObject C := ComonadSimplicialResolution.diagram G X
example (n : ℕ) :
    (ComonadSimplicialResolution.diagram G X).obj (Opposite.op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.power G X (n + 1) :=
  ComonadSimplicialResolution.diagram_obj G X n
example {n : ℕ} (i : Fin (n + 2)) :
    (ComonadSimplicialResolution.diagram G X).δ i =
      ComonadResolutionOperators.face G X (n + 1) i :=
  ComonadSimplicialResolution.diagram_face G X i
example {n : ℕ} (i : Fin (n + 1)) :
    (ComonadSimplicialResolution.diagram G X).σ i =
      ComonadResolutionOperators.degeneracy G X n i :=
  ComonadSimplicialResolution.diagram_degeneracy G X i
example : ComonadSimplicialResolution.diagram G X ⟶ (Functor.const _).obj X :=
  ComonadSimplicialResolution.augmentation G X
end Comonad

-- Arbitrary category with independent universes; no model structure is assumed.
section FreePath
variable (C : Type u) [Category.{v} C]
example : SimplicialObject Cat.{max u v, u} := FreePathSimplicialResolution.diagram C
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((FreePathSimplicialResolution.diagram C).map θ).toFunctor ⋙
        FreePathSimplicialResolution.projection C m = FreePathSimplicialResolution.projection C n :=
  FreePathSimplicialResolution.projection_naturality C θ
example : (FreePathSimplicialResolution.diagram C).obj (Opposite.op (SimplexCategory.mk 0)) =
    Cat.of (Paths (ULiftHom.{u} C)) := FreePathSimplicialResolution.degree_zero C
example : (FreePathSimplicialResolution.diagram C).obj (Opposite.op (SimplexCategory.mk 1)) =
    Cat.of (Paths (Paths (ULiftHom.{u} C))) := FreePathSimplicialResolution.degree_one C
end FreePath

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Simplex.PresentationDegeneracies,
    `SerrePositivity.CategoryTheory.Simplex.PresentationFaces,
    `SerrePositivity.CategoryTheory.Simplex.PresentationEquivalence,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Missing simplex presentation equivalence modules"
  logInfo m!"Simplex presentation equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
