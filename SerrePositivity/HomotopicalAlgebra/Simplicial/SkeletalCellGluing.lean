module

public import SerrePositivity.CategoryTheory.Limits.SequentialExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! # Assemble prescribed nondegenerate simplices into coherent skeletal maps

A map on the preceding skeleton and a specified map on each new simplex,
with its boundary equation, determine the next skeletal map by the actual
pushout. No replacement of the specified simplices is performed. A rule
for such choices gives one map on the whole simplicial set by recursion.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SSet.relativeCellComplexOfMono

namespace SerrePositivity.SimplicialModel.SkeletalCellGluing

variable {A K Q : SSet.{v}} (j : A ⟶ K) [Mono j]

abbrev stage (n : ℕ) : SSet.{v} := (SSet.skeletonOfMono j n).toSSet

abbrev boundary {n : ℕ} (c : Cell j n) : (SSet.boundary.{v} n).toSSet ⟶ stage j n :=
  c.ιSigmaBoundary ≫ t j n

abbrev cell {n : ℕ} (c : Cell j n) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ stage j (n + 1) :=
  c.ιSigmaStdSimplex ≫ b j n

@[reassoc]
lemma boundary_inclusion {n : ℕ} (c : Cell j n) :
    boundary j c ≫ (SSet.relativeCellComplexOfMono j).incl.app n =
      (SSet.boundary.{v} n).ι ≫ c.map := by
  change (c.ιSigmaBoundary ≫ t j n) ≫ (SSet.skeletonOfMono j n).ι = _
  simpa only [Category.assoc, Cell.ι_b_ι] using c.ι_t_ι_eq_ι_l_b_ι

abbrev Compatible {n : ℕ} (a : stage j n ⟶ Q)
    (f : Cell j n → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q)) : Prop :=
  ∀ c, boundary j c ≫ a = (SSet.boundary.{v} n).ι ≫ f c

omit [Mono j] in
lemma coproduct_compatible {n : ℕ} (a : stage j n ⟶ Q)
    (f : Cell j n → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    (hf : Compatible j a f) : t j n ≫ a = l j n ≫ Sigma.desc f := by
  apply Sigma.hom_ext
  intro c
  have hc := hf c
  change (c.ιSigmaBoundary ≫ t j n) ≫ a = _ at hc
  rw [Category.assoc] at hc
  simpa only [Category.assoc, Cell.ι_l_assoc, Sigma.ι_comp_desc] using hc

def glue {n : ℕ} (a : stage j n ⟶ Q)
    (f : Cell j n → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    (hf : Compatible j a f) : stage j (n + 1) ⟶ Q :=
  (SSet.relativeCellComplexOfMono.isPushout j n).desc a (Sigma.desc f)
    (coproduct_compatible j a f hf)

omit [Mono j] in
@[reassoc]
lemma glue_previous {n : ℕ} (a : stage j n ⟶ Q)
    (f : Cell j n → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    (hf : Compatible j a f) : r j n ≫ glue j a f hf = a :=
  (SSet.relativeCellComplexOfMono.isPushout j n).inl_desc _ _ _

omit [Mono j] in
@[reassoc]
lemma glue_cell {n : ℕ} (a : stage j n ⟶ Q)
    (f : Cell j n → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    (hf : Compatible j a f) (c : Cell j n) : cell j c ≫ glue j a f hf = f c := by
  rw [cell, Category.assoc, glue,
    (SSet.relativeCellComplexOfMono.isPushout j n).inr_desc, Sigma.ι_comp_desc]

omit [Mono j] in
/-- Ordinary individual face equations suffice for the full attaching equation. -/
lemma compatible_of_faces {n : ℕ} (a : stage j (n + 1) ⟶ Q)
    (f : Cell j (n + 1) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ Q))
    (hf : ∀ c (k : Fin (n + 2)),
      SSet.boundary.ι k ≫ boundary j c ≫ a = SSet.stdSimplex.δ k ≫ f c) :
    Compatible j a f := by
  intro c
  apply SSet.boundary.hom_ext
  intro k
  simpa only [Category.assoc, SSet.boundary.ι_ι_assoc] using hf c k

omit [Mono j] in
/-- Face compatibility is an output of the preceding skeletal map. -/
lemma attachingFaces_compatible {n : ℕ} (a : stage j (n + 2) ⟶ Q)
    (c : Cell j (n + 2)) :
    BoundaryGluing.StandardCompatible (fun k => SSet.boundary.ι k ≫ boundary j c ≫ a) :=
  BoundaryGluing.standardCompatible_of_boundary (boundary j c ≫ a)

/-- The next stage retains every supplied cell and the entire preceding skeleton. -/
abbrev Rule := ∀ (n : ℕ) (a : stage j n ⟶ Q) (c : Cell j n),
  {f : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q //
    (SSet.boundary.{v} n).ι ≫ f = boundary j c ≫ a}

variable (chooseCell : Rule (Q := Q) j) (a₀ : A ⟶ Q)

def next (n : ℕ) (a : stage j n ⟶ Q) :
    {e : stage j (n + 1) ⟶ Q // r j n ≫ e = a} :=
  ⟨glue j a (fun c => (chooseCell n a c).val) (fun c => (chooseCell n a c).property.symm),
    glue_previous j a _ _⟩

abbrev initial : stage j 0 ⟶ Q := (SSet.relativeCellComplexOfMono j).isoBot.hom ≫ a₀

def assembledStage (n : ℕ) : stage j n ⟶ Q :=
  SequentialExtension.stage (SSet.relativeCellComplexOfMono j).F Q
    (next j chooseCell) (initial j a₀) n

def assemble : K ⟶ Q :=
  SequentialExtension.descend (SSet.relativeCellComplexOfMono j).F Q
    (next j chooseCell) (initial j a₀)
    (Cocone.mk K (SSet.relativeCellComplexOfMono j).incl)
    (SSet.relativeCellComplexOfMono j).isColimit

@[reassoc]
lemma assemble_stage (n : ℕ) :
    (SSet.relativeCellComplexOfMono j).incl.app n ≫ assemble j chooseCell a₀ =
      assembledStage j chooseCell a₀ n :=
  SequentialExtension.descend_stage (SSet.relativeCellComplexOfMono j).F Q
    (next j chooseCell) (initial j a₀)
    (Cocone.mk K (SSet.relativeCellComplexOfMono j).incl)
    (SSet.relativeCellComplexOfMono j).isColimit n

@[reassoc]
lemma assemble_initial : j ≫ assemble j chooseCell a₀ = a₀ := by
  calc
    j ≫ assemble j chooseCell a₀ =
        ((SSet.relativeCellComplexOfMono j).isoBot.inv ≫
          (SSet.relativeCellComplexOfMono j).incl.app 0) ≫ assemble j chooseCell a₀ :=
      congrArg (fun q => q ≫ assemble j chooseCell a₀)
        (SSet.relativeCellComplexOfMono j).fac.symm
    _ = a₀ := by
      rw [Category.assoc, assemble_stage]
      exact Iso.inv_hom_id_assoc (SSet.relativeCellComplexOfMono j).isoBot a₀

/-- The global map uses the actual supplied simplex, not a new filler of its boundary. -/
@[reassoc]
lemma assemble_cell {n : ℕ} (c : Cell j n) :
    c.map ≫ assemble j chooseCell a₀ =
      (chooseCell n (assembledStage j chooseCell a₀ n) c).val := by
  calc
    c.map ≫ assemble j chooseCell a₀ =
        (cell j c ≫ (SSet.relativeCellComplexOfMono j).incl.app (n + 1)) ≫
          assemble j chooseCell a₀ :=
      congrArg (fun q => q ≫ assemble j chooseCell a₀) c.ι_b_ι.symm
    _ = cell j c ≫ assembledStage j chooseCell a₀ (n + 1) := by
      rw [Category.assoc, assemble_stage]
    _ = _ := glue_cell j (assembledStage j chooseCell a₀ n)
      (fun c => (chooseCell n (assembledStage j chooseCell a₀ n) c).val)
      (fun c => (chooseCell n (assembledStage j chooseCell a₀ n) c).property.symm) c


lemma attaching_boundary {n : ℕ} (c : Cell j n) :
    boundary j c ≫ assembledStage j chooseCell a₀ n =
      (SSet.boundary.{v} n).ι ≫ c.map ≫ assemble j chooseCell a₀ := by
  rw [← assemble_stage]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ assemble j chooseCell a₀) (boundary_inclusion j c)).trans
      (Category.assoc _ _ _))

/-- Prescribe individual simplices; use them whenever their actual attaching boundary matches. -/
def override (prescribed : ∀ n, Cell j n →
    Option (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q)) : Rule (Q := Q) j := by
  classical
  intro n a c
  exact match prescribed n c with
    | none => chooseCell n a c
    | some s => if h : (SSet.boundary.{v} n).ι ≫ s = boundary j c ≫ a then
        ⟨s, h⟩ else chooseCell n a c

omit [Mono j] in
lemma override_eq (prescribed : ∀ n, Cell j n →
    Option (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    {n : ℕ} (a : stage j n ⟶ Q) (c : Cell j n)
    (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q)
    (hs : prescribed n c = some s)
    (h : (SSet.boundary.{v} n).ι ≫ s = boundary j c ≫ a) :
    (override j chooseCell prescribed n a c).val = s := by
  classical
  simp only [override, hs, dite_eq_left h]

/-- A prescribed cell with boundary in A is retained by the global recursion. -/
lemma assemble_prescribed (prescribed : ∀ n, Cell j n →
    Option (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q))
    {n : ℕ} (c : Cell j n)
    (s : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ Q)
    (hs : prescribed n c = some s) (q : (SSet.boundary.{v} n).toSSet ⟶ A)
    (hq : q ≫ j = (SSet.boundary.{v} n).ι ≫ c.map)
    (ha : q ≫ a₀ = (SSet.boundary.{v} n).ι ≫ s) :
    c.map ≫ assemble j (override j chooseCell prescribed) a₀ = s := by
  rw [assemble_cell]
  apply override_eq j chooseCell prescribed _ c s hs
  calc
    (SSet.boundary.{v} n).ι ≫ s = q ≫ a₀ := ha.symm
    _ = q ≫ j ≫ assemble j (override j chooseCell prescribed) a₀ := by
      rw [assemble_initial]
    _ = (SSet.boundary.{v} n).ι ≫ c.map ≫
        assemble j (override j chooseCell prescribed) a₀ := by
      rw [← Category.assoc, hq, Category.assoc]
    _ = _ := (attaching_boundary j (override j chooseCell prescribed) a₀ c).symm

end SerrePositivity.SimplicialModel.SkeletalCellGluing
