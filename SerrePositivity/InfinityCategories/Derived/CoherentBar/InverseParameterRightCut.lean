module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawRightHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents
/-!
概要：逆構成のパラメーターで切った HA 右因子を定値側の成分へ直し、最後の切断以外で消去する。
方針：右区間の尾部集合の像と、定値単体の単位・零の成分公式を使う。
規約：末尾の切断では実 dg 単位を保持する。
使われ方：パラメーター側の切断合成を最後の標準面へまとめる。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseFullRight_parameter {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      ((InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) N) (m + 1)).hom
        (dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((dgCoherentBarParameterTail j).card : ℤ)) (dgCoherentBarParameterTail_two j)
        (dgCoherentBarParameterTail_min j) (dgCoherentBarParameterTail_max j) rfl) := by
  let T := (dgCoherentBarInverseRawData R D F hMC N f s)
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
  have hPure := dgCoherentBarInverseRawData_pure_right_hom_heq R D F hMC N f s L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (dgCoherentBarParameterTail_two j) (dgCoherentBarParameterTail_min j)
    (dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarInverseFullRight_parameter_zero {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      (0 : GradedHom R (N)
        (N)
        (2 - ((dgCoherentBarParameterTail j).card : ℤ))) := by
  refine (dgCoherentBarInverseFullRight_parameter R D F hMC N f s j).trans ?_
  apply dgCoherentBarConstant_hom_zero
  rw [dgCoherentBarParameterTail_card]
  have hne : j.val ≠ m := fun h => hj (Fin.ext h)
  have := j.isLt
  omega

lemma dgCoherentBarInverseFullRight_parameter_unit {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    HEq (dgCoherentBarFullRight
      (dgCoherentBarInverseRawData R D F hMC N f s) ((Fin.last m).natAdd n))
      (unitElement R (N)).val := by
  refine (dgCoherentBarInverseFullRight_parameter R D F hMC N f s (Fin.last m)).trans ?_
  apply dgCoherentBarConstant_hom_unit
  rw [dgCoherentBarParameterTail_card]
  simp

end SerrePositivity.InfinityCategories
