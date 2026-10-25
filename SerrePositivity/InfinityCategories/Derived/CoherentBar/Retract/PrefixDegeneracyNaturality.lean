module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneratePrefixCoefficients
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarPrefixOrder_degeneracy_before {n : ℕ}
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ j.val) :
    SimplexCategory.mkHom (dgCoherentBarPrefixOrder (n + 1) k (by omega)) ≫
      SimplexCategory.σ j =
    SimplexCategory.mkHom (dgCoherentBarPrefixOrder n k (by omega)) := by
  ext a
  have ha : a.val < k + 1 := a.isLt
  change (j.predAbove (dgCoherentBarPrefixOrder (n + 1) k (by omega) a)).val = a.val
  rw [Fin.predAbove_of_le_castSucc j _ (by change a.val ≤ j.val; omega)]
  rfl

lemma dgCoherentBarPrefix_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ j.val) :
    dgCoherentBarPrefix (I.σ j s) k (by omega) =
      dgCoherentBarPrefix s k (by omega) := by
  have h := congrArg (fun f => I.map f.op s)
    (dgCoherentBarPrefixOrder_degeneracy_before j k hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at h
  exact congrArg (fun t => (⟨k, t⟩ : dgCoherentBarIndex I)) h

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixHom_degeneracy_before {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ j.val) :
    HEq (dgCoherentBarPrefixHom R D F (I.σ j s) k (by omega))
      (dgCoherentBarPrefixHom R D F s k (by omega)) := by
  have hp := congrArg (fun f => I.map f.op s)
    (dgCoherentBarPrefixOrder_degeneracy_before j (k + 1) hk)
  simp only [op_comp, CategoryTheory.Functor.map_comp, types_comp_apply] at hp
  have ht : HEq
      (coherentDiagramTop F (dgCoherentBarPrefix (I.σ j s) (k + 1) (by omega)).2)
      (coherentDiagramTop F (dgCoherentBarPrefix s (k + 1) (by omega)).2) := by
    dsimp only [dgCoherentBarPrefix, SimplicialObject.σ]
    rw [hp]
  unfold dgCoherentBarPrefixHom
  exact (gradedHomTransport_heq _ _ _ _).trans
    (ht.trans (gradedHomTransport_heq _ _ _ _).symm)

end SerrePositivity.InfinityCategories
