module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyPureHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCuts
/-!
概要：混合 HA 項を元の内部頂点で切った左因子は、正規化 native 単体の同じ左因子。
方針：両方の切断集合を先頭部分集合の像へ直し、純粋な左面の成分比較を使う。
規約：パラメーターの次数を制限しない。
使われ方：元の単体側の HA 切断合成を高次 Hom の後合成へ因数分解する。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyFullLeft_source {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) (i : Fin n) :
    HEq (dgCoherentBarFullLeft
      (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (i.castAdd m))
      (dgCoherentBarFullLeft (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i) := by
  let T := (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  let S := (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let K : Finset (Fin (n + 1)) := Finset.univ.filter (· ≤ i.succ)
  have hc : K.card = i.val + 2 := by
    change ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ i.succ)).card = _
    rw [dgCoherentBarPrefix_card]
    rfl
  have hK : 2 ≤ K.card := by omega
  have h0 : (0 : Fin (n + 1)) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩
  have ha : (0 : Fin (n + 1)) = K.min' (Index.nonempty hK) :=
    le_antisymm (Fin.zero_le _) (Finset.min'_le _ 0 h0)
  have hj : i.succ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hb : i.succ = K.max' (Index.nonempty hK) :=
    le_antisymm (Finset.le_max' _ _ hj)
      (Finset.max'_le _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2))
  have hSetT : K.image (dgCoherentBarJoinLeft n m) =
      (Finset.univ : Finset (Fin (n + m + 2))).filter (· ≤ (i.castAdd m).succ.castSucc) := by
    have h := dgCoherentBarJoinSubset_filter_le_left
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 1))) i.succ
    rw [dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hSetS : K.image Fin.castSucc =
      (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ i.succ.castSucc) := by
    have h := dgCoherentBarJoinSubset_filter_le_left
      (Finset.univ : Finset (Fin (n + 1))) (Finset.univ : Finset (Fin 1)) i.succ
    rw [dgCoherentBarJoinSubset_univ] at h
    exact h.symm
  have hdT : (2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
      (· ≤ (i.castAdd m).succ.castSucc)).card : ℤ)) = 2 - (K.card : ℤ) := by
    rw [← hSetT, Finset.card_image_of_injective _ (dgCoherentBarJoinLeft_injective n m)]
  have hdS : (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
      (· ≤ i.succ.castSucc)).card : ℤ)) = 2 - (K.card : ℤ) := by
    rw [← hSetS, Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
  have hPure := dgCoherentBarCoconeFamilySimplex_pure_left_hom_heq R D F y hMC c s
    K 0 i.succ (2 - (K.card : ℤ)) hK ha hb rfl
  refine HEq.trans ?_ (hPure.trans ?_)
  · exact SimplexData.hom_heq_of_indices_degree T hSetT.symm rfl rfl hdT
  · exact SimplexData.hom_heq_of_indices_degree S hSetS rfl rfl hdS.symm

end SerrePositivity.InfinityCategories
