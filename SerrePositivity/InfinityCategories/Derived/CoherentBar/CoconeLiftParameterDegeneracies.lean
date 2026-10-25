module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftDegeneracies
/-!
概要：動く右面を持つ余錐族について、パラメーターの退化写像で、高次余錐族から回収した Hom が零になる。
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

lemma dgCoherentBarCoconeLiftColumn_parameter_degeneracy {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarIndex I) (i : Fin (m + 1)) :
    dgCoherentBarCoconeLiftColumn R D F ((sliceUnder F).σ i c) s = 0 := by
  rcases s with ⟨n, s⟩
  have hn : ¬Function.Injective i.predAboveOrderHom := by
    intro hi
    have hc := Fintype.card_le_of_injective i.predAboveOrderHom hi
    simp only [Fintype.card_fin] at hc
    omega
  have hβ := dgCoherentBarJoinOrderMap_not_injective_right
    (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) i.predAboveOrderHom hn
  have he := dgCoherentBarCoconeLiftSimplex_map R D F c s
    (𝟙 ⦋n⦌) (SimplexCategory.σ i)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at he
  change dgCoherentBarCoconeLiftSimplex R D F ((sliceUnder F).σ i c) s =
    (dgCoherentBarCoconeLiftSimplex R D F c s).pullback
      (dgCoherentBarJoinOrderMap OrderHom.id i.predAboveOrderHom) at he
  have hz : (dgCoherentBarCoconeLiftSimplex R D F
      ((sliceUnder F).σ i c) s).hom
      Finset.univ 0 (Fin.last (n + (m + 1) + 1)) (-((m + 1 : ℕ) : ℤ) - (n : ℤ))
      (coherentDiagramTop_card (n + (m + 1))) (coherentDiagramTop_min (n + (m + 1)))
      (coherentDiagramTop_max (n + (m + 1))) (by simp; omega) = 0 := by
    rw [he]
    exact SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _
      (fun hi => hβ (fun a b hab => hi (Finset.mem_univ _) (Finset.mem_univ _) hab))
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  unfold dgCoherentBarCoconeLiftColumn
  rw [hz, dgCoherentBarGradedTransport_zero]

lemma dgCoherentBarCoconeLiftHom_parameter_degeneracy
    (hMC : dgCoherentBarMaurerCartan R D F) {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (i : Fin (m + 1)) :
    dgCoherentBarCoconeLiftHom R D F hMC ((sliceUnder F).σ i c) = 0 := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeLiftTarget R D F ((sliceUnder F).σ i c)) (-((m + 1 : ℕ) : ℤ))).injective
  rw [map_zero]
  funext s
  simp only [dgCoherentBarCoconeLiftHom, LinearEquiv.apply_symm_apply, Pi.zero_apply]
  exact dgCoherentBarCoconeLiftColumn_parameter_degeneracy R D F c s.val i

lemma dgCoherentBarCoconeLiftHom_heq_of_index_eq
    (hMC : dgCoherentBarMaurerCartan R D F) {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (c' : (sliceUnder F) _⦋n⦌)
    (h : (⟨m, c⟩ : dgCoherentBarIndex (sliceUnder F)) = ⟨n, c'⟩) :
    HEq (dgCoherentBarCoconeLiftHom R D F hMC c)
      (dgCoherentBarCoconeLiftHom R D F hMC c') := by
  cases h
  rfl

lemma dgCoherentBarCoconeLiftHom_degenerate
    (hMC : dgCoherentBarMaurerCartan R D F)
    (a : dgCoherentBarDegenerateIndex (sliceUnder F)) :
    dgCoherentBarCoconeLiftHom R D F hMC a.val.2 = 0 := by
  rcases a with ⟨⟨n, c⟩, hc⟩
  cases n with
  | zero => simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hc
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ] at hc
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.mp hc
    exact dgCoherentBarCoconeLiftHom_parameter_degeneracy R D F hMC c i

end SerrePositivity.InfinityCategories
