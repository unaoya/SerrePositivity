module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementHomotopy
public import Mathlib.Algebra.Homology.Homotopy

/-!
概要：Čech H 上の細分写像は、細分の添字の選択に依存しない。
方針：制限付き整数鎖の比較を複体の Homotopy にまとめる。
規約：被覆性・アフィン性を使わず、二つの細分の包含だけを使う。
使われ方：共通アフィン細分による比較を、選択によらない射として扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v w
variable {X : Type u} [TopologicalSpace X] {R : Type w} [CommRing R]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X) (V : κ → Opens X)
variable (ρ σ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (hσ : ∀ j, V j ≤ U (σ j))

/-- 細分比較の複体としてのホモトピーの成分。 -/
def openCoverCechRefinementHomotopyComponent (i j : ℕ) :
    (fullCechComplex (openCoverCechDiagram P U)).X i ⟶
      (fullCechComplex (openCoverCechDiagram P V)).X j :=
  if e : j + 1 = i then
    eqToHom (congrArg (fullCechComplex (openCoverCechDiagram P U)).X e.symm) ≫
      ModuleCat.ofHom (openCoverCechRefinementHomotopyTerm P U V ρ σ (j + 1))
  else 0

/-- 連続する次数での比較ホモトピーの成分。 -/
theorem openCoverCechRefinementHomotopyComponent_succ (j : ℕ) :
    openCoverCechRefinementHomotopyComponent P U V ρ σ (j + 1) j =
      ModuleCat.ofHom (openCoverCechRefinementHomotopyTerm P U V ρ σ (j + 1)) := by
  unfold openCoverCechRefinementHomotopyComponent
  rw [dite_eq_left rfl, eqToHom_refl]
  rfl

/-- 同じ細分の二つの添字の選択は、コチェイン写像としてホモトピック。 -/
def openCoverCechRefinementHomotopy :
    Homotopy (openCoverCechRefinementMap P U V σ hσ)
      (openCoverCechRefinementMap P U V ρ hρ) where
  hom := openCoverCechRefinementHomotopyComponent P U V ρ σ
  zero i j h := by
    have e : ¬ j + 1 = i := h
    exact dite_eq_right e
  comm i := by
    rw [Homotopy.dNext_cochainComplex, openCoverCechRefinementHomotopyComponent_succ]
    have h := openCoverCechRefinementHomotopyTerm_identity P U V ρ σ hρ hσ i
    cases i with
    | zero =>
      rw [Homotopy.prevD_zero_cochainComplex, add_zero]
      rw [openCoverCechRefinementHomotopyTerm_zero, LinearMap.comp_zero, add_zero] at h
      simp only [fullCechComplex, CochainComplex.of_d, openCoverCechRefinementMap,
        CochainComplex.ofHom]
      apply ModuleCat.hom_ext
      exact (eq_sub_iff_add_eq.mp h).symm
    | succ i =>
      rw [Homotopy.prevD_succ_cochainComplex,
        openCoverCechRefinementHomotopyComponent_succ]
      simp only [fullCechComplex, CochainComplex.of_d, openCoverCechRefinementMap,
        CochainComplex.ofHom]
      apply ModuleCat.hom_ext
      exact (eq_sub_iff_add_eq.mp h).symm

/-- Čech H 上の細分の射は、細分の添字の選択によらない。 -/
theorem openCoverCechRefinement_homologyMap_eq (q : ℕ) :
    HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q =
      HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V σ hσ) q :=
  ((openCoverCechRefinementHomotopy P U V ρ σ hρ hσ).homologyMap_eq q).symm

end SerrePositivity.AlgebraicGeometry
