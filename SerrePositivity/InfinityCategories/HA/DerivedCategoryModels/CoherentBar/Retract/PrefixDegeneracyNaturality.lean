module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneratePrefixCoefficients
/-!
概要：切断が重複頂点より前にあるとき、退化前後の prefix の全高次係数は一致する。
方針：元の順序写像の厳密な等式を先に示し、端点輸送を異種等号で保持する。
規約：coherent な高次係数を辺の通常合成で置換しない。
使われ方：正規化境界で二つの prefix 和を相殺するための係数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarPrefixOrder_degeneracy_before {n : ℕ}
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ j.val) :
    SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k (by omega)) ≫
      SimplexCategory.σ j =
    SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n k (by omega)) := by
  ext a
  have ha : a.val < k + 1 := a.isLt
  change (j.predAbove (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k (by omega) a)).val = a.val
  rw [Fin.predAbove_of_le_castSucc j _ (by change a.val ≤ j.val; omega)]
  rfl

lemma dgCoherentBarPrefix_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ j.val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ j s) k (by omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s k (by omega) := by
  have h := congrArg (fun f => I.map f.op s)
    (dgCoherentBarPrefixOrder_degeneracy_before j k hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  exact congrArg (fun t => (⟨k, t⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)) h

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixHom_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F (I.σ j s) k (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega)) := by
  have hp := congrArg (fun f => I.map f.op s)
    (dgCoherentBarPrefixOrder_degeneracy_before j (k + 1) hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at hp
  have ht : HEq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ j s) (k + 1) (by omega)).2)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s (k + 1) (by omega)).2) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix, SimplicialObject.σ]
    rw [hp]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _).trans
    (ht.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
