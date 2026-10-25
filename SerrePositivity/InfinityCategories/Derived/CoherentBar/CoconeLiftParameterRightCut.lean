module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterData
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftPureHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents
/-!
概要：パラメーターで切った HA 右因子を、動く右面の実成分へ直す。
方針：右区間の尾部集合の像と、純粋右面の成分比較を使う。
規約：定値性を仮定せず、実 dg HA 成分を保持する。
使われ方：全切断合成を型付きの回収 HA 項へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCoconeLiftFullRight_parameter {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (((sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).hom
        (dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((dgCoherentBarParameterTail j).card : ℤ)) (dgCoherentBarParameterTail_two j)
        (dgCoherentBarParameterTail_min j) (dgCoherentBarParameterTail_max j) rfl) := by
  let T := (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let L := dgCoherentBarParameterTail j
  have hj : dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hl : dgCoherentBarJoinRight n (m + 1) (Fin.last (m + 1)) =
      Fin.last (n + (m + 1) + 1) := Fin.ext (by
    change n + 1 + (m + 1) = n + (m + 1) + 1
    omega)
  have hSet : L.image (dgCoherentBarJoinRight n (m + 1)) =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
        ((j.natAdd n).succ.castSucc ≤ ·) := by
    have h := dgCoherentBarJoinSubset_filter_right_le
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hd : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      ((j.natAdd n).succ.castSucc ≤ ·)).card : ℤ)) = 2 - (L.card : ℤ) := by
    rw [← hSet, Finset.card_image_of_injective _
      (dgCoherentBarJoinRight_injective n (m + 1))]
  have hPure := dgCoherentBarCoconeLiftSimplex_pure_right_hom_heq R D F c s L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (dgCoherentBarParameterTail_two j) (dgCoherentBarParameterTail_min j)
    (dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarCoconeLiftFullRight_parameter_tail {m n : ℕ}
    (c : (sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (dgCoherentBarCoconeLiftParameterTail R D F c j) := by
  refine (dgCoherentBarCoconeLiftFullRight_parameter R D F c s j).trans ?_
  unfold dgCoherentBarCoconeLiftParameterTail
  exact (gradedHomTransport_heq _ _ _ _).symm

end SerrePositivity.InfinityCategories
