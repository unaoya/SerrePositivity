module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarSubsetCuts
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarCoefficients
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents

/-!
概要：bar の prefix 係数を、元の coherent 単体の同じ頂点集合の成分へ戻す。
方針：実 prefix 制限の自然性と単射による Hom の引き戻しを使い、二つの端点輸送を除く。
規約：全高次成分とその次数を保持する。
使われ方：末端への HA 右辺の左切断と、元の bar の prefix ブロックの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarPrefixRawComponent {n : ℕ} (σ : I _⦋n⦌) (k : ℕ) (h : k + 1 ≤ n) :
    GradedHom R ((coherentDiagramSimplex F σ).obj 0)
      ((coherentDiagramSimplex F σ).obj ⟨k + 1, by omega⟩) (-(k : ℤ)) := by
  let α := dgCoherentBarPrefixOrder n (k + 1) h
  have hi : Set.InjOn α ((Finset.univ : Finset (Fin (k + 2))) : Set (Fin (k + 2))) :=
    (dgCoherentBarPrefixOrder_injective n (k + 1) h).injOn
  exact (coherentDiagramSimplex F σ).hom (Finset.univ.image α) (α 0) (α (Fin.last (k + 1)))
    (-(k : ℤ)) (Index.image_two hi (coherentDiagramTop_card k))
    (Index.image_min α.monotone (by rw [coherentDiagramTop_min k]; exact Finset.univ.isLeast_min' _) _)
    (Index.image_max α.monotone (by rw [coherentDiagramTop_max k]; exact Finset.univ.isGreatest_max' _) _)
    (by rw [Finset.card_image_of_injOn hi]; simp; omega)

lemma dgCoherentBarPrefixHom_heq_rawComponent {n : ℕ} (σ : I _⦋n⦌) (k : ℕ)
    (h : k + 1 ≤ n) :
    HEq (dgCoherentBarPrefixHom R D F σ k h) (dgCoherentBarPrefixRawComponent R D F σ k h) := by
  have hf : HEq (dgCoherentBarPrefixHom R D F σ k h)
      (coherentDiagramTop F (n := k) (dgCoherentBarPrefix σ (k + 1) h).2) :=
    gradedHomTransport_heq (A := R) (D := RightModule R D) _ _ _ _
  have ht : HEq (coherentDiagramTop F (n := k) (dgCoherentBarPrefix σ (k + 1) h).2)
      (coherentDiagramTopRaw F (n := k) (dgCoherentBarPrefix σ (k + 1) h).2) :=
    gradedHomTransport_heq (A := R) (D := RightModule R D) _ _ _ _
  let α := dgCoherentBarPrefixOrder n (k + 1) h
  have hp : (coherentDiagramSimplex F (n := k + 1) (dgCoherentBarPrefix σ (k + 1) h).2).toSimplexData =
      (coherentDiagramSimplex F σ).toSimplexData.pullback α :=
    congrArg DGNerve.Simplex.toSimplexData (coherentDiagramSimplex_map F α σ)
  have hh := SimplexData.hom_heq_of_eq hp Finset.univ 0 (Fin.last (k + 1)) (-(k : ℤ))
    (coherentDiagramTop_card k) (coherentDiagramTop_min k) (coherentDiagramTop_max k) (by simp; omega)
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    (dgCoherentBarPrefixOrder_injective n (k + 1) h).injOn] at hh
  exact hf.trans (ht.trans hh)

end SerrePositivity.InfinityCategories
