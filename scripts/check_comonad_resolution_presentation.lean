import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation

universe v u
noncomputable section
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

-- All degrees and all six relations, for an arbitrary comonad without a model structure.
section General
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)
open ComonadResolutionOperators

example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    face G X (n + 1) j.succ ≫ face G X n i =
      face G X (n + 1) i.castSucc ≫ face G X n j := face_face G X n i j h

example (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X n i ≫ face G X (n + 1) i.castSucc = 𝟙 _ :=
  degeneracy_face_self G X n i

example (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X n i ≫ face G X (n + 1) i.succ = 𝟙 _ :=
  degeneracy_face_succ G X n i

example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    degeneracy G X n j ≫ degeneracy G X (n + 1) i.castSucc =
      degeneracy G X n i ≫ degeneracy G X (n + 1) j.succ :=
  degeneracy_degeneracy G X n i j h

example (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    degeneracy G X (n + 1) j.succ ≫ face G X (n + 2) i.castSucc =
      face G X (n + 1) i ≫ degeneracy G X n j := degeneracy_face_le G X n i j h

example (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    degeneracy G X (n + 1) j.castSucc ≫ face G X (n + 2) i.succ =
      face G X (n + 1) i ≫ degeneracy G X n j := degeneracy_face_gt G X n i j h

example : SimplexCategoryGenRelᵒᵖ ⥤ C := ComonadResolutionPresentation.diagram G X

example (n : ℕ) :
    (ComonadResolutionPresentation.diagram G X).obj
      (Opposite.op (SimplexCategoryGenRel.mk n)) = power G X (n + 1) :=
  ComonadResolutionPresentation.diagram_obj G X n

example {n : ℕ} (i : Fin (n + 2)) :
    (ComonadResolutionPresentation.diagram G X).map (SimplexCategoryGenRel.δ i).op =
      face G X (n + 1) i := ComonadResolutionPresentation.diagram_face G X i

example {n : ℕ} (i : Fin (n + 1)) :
    (ComonadResolutionPresentation.diagram G X).map (SimplexCategoryGenRel.σ i).op =
      degeneracy G X n i := ComonadResolutionPresentation.diagram_degeneracy G X i

example : ComonadResolutionPresentation.diagram G X ⟶ (Functor.const _).obj X :=
  ComonadResolutionPresentation.augmentationNatTrans G X
end General

-- Independent object/Hom universes; no source model, no lifted model structure.
section FreePath
variable (C : Type u) [Category.{v} C]

example : SimplexCategoryGenRelᵒᵖ ⥤ Cat.{max u v, u} :=
  FreePathResolutionPresentation.diagram C

example {n m : SimplexCategoryGenRelᵒᵖ} (θ : n ⟶ m) :
    ((FreePathResolutionPresentation.diagram C).map θ).toFunctor ⋙
        FreePathResolutionPresentation.projection C m =
      FreePathResolutionPresentation.projection C n :=
  FreePathResolutionPresentation.projection_naturality C θ

example : (FreePathResolutionPresentation.diagram C).obj
    (Opposite.op (SimplexCategoryGenRel.mk 0)) = Cat.of (Paths (ULiftHom.{u} C)) :=
  FreePathResolutionPresentation.degree_zero C

example : (FreePathResolutionPresentation.diagram C).obj
    (Opposite.op (SimplexCategoryGenRel.mk 1)) = Cat.of (Paths (Paths (ULiftHom.{u} C))) :=
  FreePathResolutionPresentation.degree_one C
end FreePath

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionOperators,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation]
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
    throwError "Missing comonad resolution presentation modules"
  logInfo m!"Comonad resolution presentation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
