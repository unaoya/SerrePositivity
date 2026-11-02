module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGradedSplit
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutZero
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
概要：h-projective 頂点の coherent bar の各有限次元段階は h-projective。
方針：零段階から始め、次数付き分裂拡大と各次元層の射影性で帰納する。
規約：高次 HA 成分を持つ元の coherent 図式を用いる。
使われ方：全 bar の射影性を与える可算段階列。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCutModule_projective
    (hG : ∀ s : I _⦋0⦌, moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (coherentDiagramVertex G s))) (n : ℕ) :
    moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n)) := by
  induction n with
  | zero => exact dgCoherentBarCutZero_projective R D G hG
  | succ n ih =>
    exact (dgCoherentBarCutGradedSplit R D G n).homotopicallyProjective R D ih
      (dgCoherentBarLayerGraded_projective R D G hG (n + 1))

end SerrePositivity.InfinityCategories
