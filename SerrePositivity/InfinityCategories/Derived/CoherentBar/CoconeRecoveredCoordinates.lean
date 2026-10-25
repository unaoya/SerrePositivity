module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubset
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawRestrictions
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinPointIndex
/-!
概要：回収した一点下のデータの左右制限と全混合成分を計算する。
方針：join 貼り合わせの実制限と混合成分の計算則を直接使う。
規約：この段階では回収データの HA 方程式を仮定しない。
使われ方：持ち上げ余錐のパラメーター側 HA 項との照合。
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
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_left {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback (dgCoherentBarJoinLeft 0 n) =
      (Simplex.vertex (A := R) (dgCoherentBarNormalizedModule R D F hMC)).toSimplexData :=
  dgCoherentBarJoinRawData_left _ _ _

lemma dgCoherentBarCoconeRecoveredRawData_right {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback (dgCoherentBarJoinRight 0 n) =
      ((sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).toSimplexData :=
  dgCoherentBarJoinRawData_right _ _ _

lemma dgCoherentBarCoconeRecoveredRawData_source {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj 0 =
      dgCoherentBarNormalizedModule R D F hMC := by
  exact congrArg (fun t : SimplexData R (RightModule R D) 0 => t.obj 0)
    (dgCoherentBarCoconeRecoveredRawData_left R D F hMC c)

lemma dgCoherentBarCoconeRecoveredRawData_target {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj (Fin.last (0 + n + 1)) =
      dgCoherentBarCoconeLiftTarget R D F c := by
  have h := congrArg (fun t : SimplexData R (RightModule R D) n => t.obj (Fin.last n))
    (dgCoherentBarCoconeRecoveredRawData_right R D F hMC c)
  have he : dgCoherentBarJoinRight 0 n (Fin.last n) = Fin.last (0 + n + 1) :=
    Fin.ext (by dsimp [dgCoherentBarJoinRight, joinRightOrderHom]; omega)
  change (dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj
    (dgCoherentBarJoinRight 0 n (Fin.last n)) = _ at h
  rwa [he] at h

lemma dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq {n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) (J : Finset (Fin (n + 1))) (hJ : J.Nonempty)
    (a b : Fin (0 + n + 1 + 1)) (k : ℤ)
    (hS : 2 ≤ (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).card)
    (ha : a = (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).min' (Index.nonempty hS))
    (hb : b = (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).max' (Index.nonempty hS))
    (hk : k = 2 - ((dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).card : ℤ)) :
    HEq ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom
      (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J) a b k hS ha hb hk)
      (dgCoherentBarCoconeLiftSubsetHom R D F hMC c J k hJ (by
        rw [dgCoherentBarJoinSubset_card] at hk
        simp only [Finset.card_univ, Fintype.card_fin] at hk
        omega)) :=
  dgCoherentBarJoinRawData_mixed_hom_heq _ _ _ Finset.univ J Finset.univ_nonempty hJ
    a b k hS ha hb hk

lemma dgCoherentBarCoconeRecoveredRawData_full_hom_heq {n : ℕ}
    (c : (sliceUnder F) _⦋n⦌) :
    HEq ((dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom Finset.univ
      0 (Fin.last (0 + n + 1)) (-(n : ℤ))
      (coherentDiagramTop_card (0 + n)) (coherentDiagramTop_min (0 + n))
      (coherentDiagramTop_max (0 + n)) (by simp; omega))
      (dgCoherentBarCoconeLiftHom R D F hMC c) := by
  let S := (dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1))
    (Finset.univ : Finset (Fin (n + 1))))
  have hSet : S = Finset.univ := dgCoherentBarJoinSubset_univ 0 n
  have hS : 2 ≤ S.card := by rw [hSet]; simp
  have ha : (0 : Fin (0 + n + 1 + 1)) = S.min' (Index.nonempty hS) := by
    simpa only [hSet] using coherentDiagramTop_min (0 + n)
  have hb : Fin.last (0 + n + 1) = S.max' (Index.nonempty hS) := by
    simpa only [hSet] using coherentDiagramTop_max (0 + n)
  have hk : -(n : ℤ) = 2 - (S.card : ℤ) := by rw [hSet]; simp; omega
  have hMixed := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c
    Finset.univ Finset.univ_nonempty 0 (Fin.last (0 + n + 1)) (-(n : ℤ)) hS ha hb hk
  have hSubset := dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC c
    Finset.univ (-(n : ℤ)) Finset.univ_nonempty (by simp) (by simp :
      (Finset.univ : Finset (Fin (n + 1))).card = n + 1)
  rw [dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at hSubset
  refine HEq.trans ?_ (hMixed.trans hSubset)
  exact SimplexData.hom_heq_of_indices_degree _ hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories
