module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubset
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawRestrictions
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPointIndex
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_left {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft 0 n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)).toSimplexData :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData_left _ _ _

lemma dgCoherentBarCoconeRecoveredRawData_right {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋n⦌) c).toSimplexData :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData_right _ _ _

lemma dgCoherentBarCoconeRecoveredRawData_source {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj 0 =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC := by
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) 0 => t.obj 0)
    (dgCoherentBarCoconeRecoveredRawData_left R D F hMC c)

lemma dgCoherentBarCoconeRecoveredRawData_target {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj (Fin.last (0 + n + 1)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c := by
  have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) n => t.obj (Fin.last n))
    (dgCoherentBarCoconeRecoveredRawData_right R D F hMC c)
  have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n (Fin.last n) = Fin.last (0 + n + 1) :=
    Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom]; omega)
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).obj
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n (Fin.last n)) = _ at h
  rwa [he] at h

lemma dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (J : Finset (Fin (n + 1))) (hJ : J.Nonempty)
    (a b : Fin (0 + n + 1 + 1)) (k : ℤ)
    (hS : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) J) a b k hS ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c J k hJ (by
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card] at hk
        simp only [Finset.card_univ, Fintype.card_fin] at hk
        omega)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData_mixed_hom_heq _ _ _ Finset.univ J Finset.univ_nonempty hJ
    a b k hS ha hb hk

lemma dgCoherentBarCoconeRecoveredRawData_full_hom_heq {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).hom Finset.univ
      0 (Fin.last (0 + n + 1)) (-(n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (0 + n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (0 + n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (0 + n)) (by simp; omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c) := by
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1))
    (Finset.univ : Finset (Fin (n + 1))))
  have hSet : S = Finset.univ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ 0 n
  have hS : 2 ≤ S.card := by rw [hSet]; simp
  have ha : (0 : Fin (0 + n + 1 + 1)) = S.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
    simpa only [hSet] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (0 + n)
  have hb : Fin.last (0 + n + 1) = S.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hS) := by
    simpa only [hSet] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (0 + n)
  have hk : -(n : ℤ) = 2 - (S.card : ℤ) := by rw [hSet]; simp; omega
  have hMixed := dgCoherentBarCoconeRecoveredRawData_mixed_hom_heq R D F hMC c
    Finset.univ Finset.univ_nonempty 0 (Fin.last (0 + n + 1)) (-(n : ℤ)) hS ha hb hk
  have hSubset := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC c
    Finset.univ (-(n : ℤ)) Finset.univ_nonempty (by simp) (by simp :
      (Finset.univ : Finset (Fin (n + 1))).card = n + 1)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at hSubset
  refine HEq.trans ?_ (hMixed.trans hSubset)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
