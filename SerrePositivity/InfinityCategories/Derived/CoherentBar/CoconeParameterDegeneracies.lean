module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDegeneracies
/-!
概要：パラメーターの退化写像で、高次余錐族から回収した Hom が零になる。
方針：join の右区間の非単射性から全混合成分を消し、Hom 成分同値の単射性を使う。
規約：元の単体の次数は任意で、パラメーター零次元を含む全退化を扱う。
使われ方：回収した成分族を正規化した写像空間の cochain として扱う。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyColumn_parameter_degeneracy {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarIndex I) (i : Fin (m + 1)) :
    dgCoherentBarCoconeFamilyColumn R D F y ((coconeMappingSpace F y).σ i c) s = 0 := by
  rcases s with ⟨n, s⟩
  have hn : ¬Function.Injective i.predAboveOrderHom := by
    intro hi
    have hc := Fintype.card_le_of_injective i.predAboveOrderHom hi
    simp only [Fintype.card_fin] at hc
    omega
  have hβ := dgCoherentBarJoinOrderMap_not_injective_right
    (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) i.predAboveOrderHom hn
  have he := dgCoherentBarCoconeFamilySimplex_map R D F y c s
    (𝟙 ⦋n⦌) (SimplexCategory.σ i)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at he
  change dgCoherentBarCoconeFamilySimplex R D F y ((coconeMappingSpace F y).σ i c) s =
    (dgCoherentBarCoconeFamilySimplex R D F y c s).pullback
      (dgCoherentBarJoinOrderMap OrderHom.id i.predAboveOrderHom) at he
  have hz : (dgCoherentBarCoconeFamilySimplex R D F y
      ((coconeMappingSpace F y).σ i c) s).hom
      Finset.univ 0 (Fin.last (n + (m + 1) + 1)) (-((m + 1 : ℕ) : ℤ) - (n : ℤ))
      (coherentDiagramTop_card (n + (m + 1))) (coherentDiagramTop_min (n + (m + 1)))
      (coherentDiagramTop_max (n + (m + 1))) (by simp; omega) = 0 := by
    rw [he]
    exact SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _
      (fun hi => hβ (fun a b hab => hi (Finset.mem_univ _) (Finset.mem_univ _) hab))
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  unfold dgCoherentBarCoconeFamilyColumn
  rw [hz, dgCoherentBarGradedTransport_zero]

lemma dgCoherentBarCoconeFamilyHom_parameter_degeneracy
    (hMC : dgCoherentBarMaurerCartan R D F) {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (i : Fin (m + 1)) :
    dgCoherentBarCoconeFamilyHom R D F hMC y ((coconeMappingSpace F y).σ i c) = 0 := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) (-((m + 1 : ℕ) : ℤ))).injective
  rw [map_zero]
  funext s
  simp only [dgCoherentBarCoconeFamilyHom, LinearEquiv.apply_symm_apply, Pi.zero_apply]
  exact dgCoherentBarCoconeFamilyColumn_parameter_degeneracy R D F y c s.val i

end SerrePositivity.InfinityCategories
