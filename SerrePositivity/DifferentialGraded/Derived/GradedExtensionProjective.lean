module
public import SerrePositivity.DifferentialGraded.Module.GradedSplitHomExact
public import SerrePositivity.DifferentialGraded.Derived.CoproductProjective
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # 全次数分裂する拡大とsemifree filtrationの有限段の射影性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma ModuleGradedSplit.homotopicallyProjective {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g)
    (hM : moduleHomotopicallyProjective A D M)
    (hP : moduleHomotopicallyProjective A D P) :
    moduleHomotopicallyProjective A D N := by
  intro T hT
  exact (s.homShortComplex_shortExact T).acyclic_X₂ (hP T hT) (hM T hT)

lemma ModuleSemifreeFiltration.stage_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.stage n) := by
  induction n with
  | zero => exact F.initial_homotopicallyProjective A D
  | succ n ih =>
    exact (F.split n).homotopicallyProjective A D ih (F.quotient_homotopicallyProjective A D n)

end SerrePositivity.DifferentialGraded
