module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterErase
/-!
概要：動く右面の全パラメーター切断の左因子を、回収前部 Hom と native 列へ分解する。
方針：任意の右前部集合の混合因数分解を使う。
規約：実際の HA 成分を用い、端点と次数を異種等号で保持する。
使われ方：全切断合成を回収データの非線形 HA 項へ移す。
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

lemma dgCoherentBarCoconeLiftFullLeft_parameter {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n))
      (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
        (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
        (z := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix j
  let v := (j.natAdd n).succ.castSucc
  have hcL : L.card = j.val + 1 := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_card j
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n (m + 1) j.castSucc = v :=
    Fin.ext (by change n + 1 + j.val = n + j.val + 1; omega)
  have hSet : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter (· ≤ v) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_le_right K
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    simp only [K] at h
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card, hcL]
    simp only [K, Finset.card_univ, Fintype.card_fin]
    omega
  have ha : (0 : Fin (n + (m + 1) + 2)) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    apply le_antisymm (Fin.zero_le _)
    apply Finset.min'_le
    rw [hSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have hb : v = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) := by
    apply le_antisymm
    · apply Finset.le_max'
      rw [hSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
    · apply Finset.max'_le
      intro x hx
      rw [hSet] at hx
      exact (Finset.mem_filter.mp hx).2
  let k : ℤ := 2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
    (· ≤ v)).card : ℤ)
  have hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ) := by rw [hSet]
  have hF := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_subset_factorization R D F hMC
    (r := n) (l := j.val) c s K L (by simp [K]) hcL
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_nonempty j) 0 v k hJ ha hb hk
  simp only [K] at hF
  have hLabel := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_univ s
  have hSource := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F) hLabel
  have hColumn := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn_heq_of_index_eq R D F hMC hLabel
  have hPrefix : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_nonempty j)
        (by rw [hcL]; push_cast; omega)) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _
  have hObj := congrArg (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_max j)
  have hComp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hSource rfl hObj rfl rfl
    (show -(j.val : ℤ) - (n : ℤ) = -(n : ℤ) + -(j.val : ℤ) by omega)
    (p := -(n : ℤ)) (q := -(j.val : ℤ)) (k := -(j.val : ℤ) - (n : ℤ))
    (p' := -(n : ℤ)) (q' := -(j.val : ℤ)) (k' := -(n : ℤ) + -(j.val : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(j.val : ℤ))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterPrefix_nonempty j) (by rw [hcL]; push_cast; omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s Finset.univ n (by simp)))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    hPrefix.symm hColumn (by omega) rfl
  refine HEq.trans ?_ (hF.trans hComp)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm rfl rfl rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
