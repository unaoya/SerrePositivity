module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawPureHom
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCuts
/-!
概要：逆構成の混合 HA 項を元の内部頂点で切った左因子は、正規化 native 単体の同じ左因子。
方針：両方の切断集合を先頭部分集合の像へ直し、純粋な左面の成分比較を使う。
規約：パラメーターの次数を制限しない。
使われ方：元の単体側の HA 切断合成を高次 Hom の後合成へ因数分解する。
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
  (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)

lemma dgCoherentBarInverseFullLeft_source {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (i : Fin n) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (i.castAdd m))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s)
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ.filter (· ≤ i.succ)
  have hc : K.card = i.val + 2 := by
    change ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ i.succ)).card = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_card]
    rfl
  have hK : 2 ≤ K.card := by omega
  have h0 : (0 : Fin (n + 1)) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have ha : (0 : Fin (n + 1)) = K.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
    le_antisymm (Fin.zero_le _) (Finset.min'_le _ 0 h0)
  have hj : i.succ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hb : i.succ = K.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK) :=
    le_antisymm (Finset.le_max' _ _ hj)
      (Finset.max'_le _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2))
  have hSetT : K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) =
      (Finset.univ : Finset (Fin (n + m + 2))).filter (· ≤ (i.castAdd m).succ.castSucc) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_le_left
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 1))) i.succ
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hSetS : K.image Fin.castSucc =
      (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ i.succ.castSucc) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_le_left
      (Finset.univ : Finset (Fin (n + 1))) (Finset.univ : Finset (Fin 1)) i.succ
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hdT : (2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
      (· ≤ (i.castAdd m).succ.castSucc)).card : ℤ)) = 2 - (K.card : ℤ) := by
    rw [← hSetT, Finset.card_image_of_injective _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective n m)]
  have hdS : (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
      (· ≤ i.succ.castSucc)).card : ℤ)) = 2 - (K.card : ℤ) := by
    rw [← hSetS, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  have hPure := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_pure_left_hom_heq R D F hMC N f s
    K 0 i.succ (2 - (K.card : ℤ)) hK ha hb rfl
  refine HEq.trans ?_ (hPure.trans ?_)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSetT.symm rfl rfl hdT
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree S hSetS rfl rfl hdS.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
