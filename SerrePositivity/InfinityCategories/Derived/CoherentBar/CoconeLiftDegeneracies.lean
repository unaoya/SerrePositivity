module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDegeneracies
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeDegenerateColumns
/-!
概要：持ち上げ余錐について、高次余錐族の混合成分は、元の単体の退化因子で消滅する。
方針：二変数 join の自然性と、非単射引き戻しの高次 HA 成分の零性を使う。
規約：余錐族の全パラメーター次数を含み、追加の閉性を仮定しない。
使われ方：非退化成分から回収した斉次 Hom を全単体の成分へ拡張する。
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

lemma dgCoherentBarCoconeLiftColumn_degeneracy {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) (i : Fin (n + 1)) :
    dgCoherentBarCoconeLiftColumn R D F c ⟨n + 1, I.σ i s⟩ = 0 := by
  have hn : ¬Function.Injective i.predAboveOrderHom := by
    intro hi
    have hc := Fintype.card_le_of_injective i.predAboveOrderHom hi
    simp only [Fintype.card_fin] at hc
    omega
  have hβ := dgCoherentBarJoinOrderMap_not_injective_left
    i.predAboveOrderHom (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) hn
  have he := dgCoherentBarCoconeLiftSimplex_map R D F c s
    (SimplexCategory.σ i) (𝟙 ⦋m⦌)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at he
  change dgCoherentBarCoconeLiftSimplex R D F c (I.σ i s) =
    (dgCoherentBarCoconeLiftSimplex R D F c s).pullback
      (dgCoherentBarJoinOrderMap i.predAboveOrderHom OrderHom.id) at he
  have hz : (dgCoherentBarCoconeLiftSimplex R D F c (I.σ i s)).hom
      Finset.univ 0 (Fin.last (n + 1 + m + 1)) (-(m : ℤ) - ((n + 1 : ℕ) : ℤ))
      (coherentDiagramTop_card (n + 1 + m)) (coherentDiagramTop_min (n + 1 + m))
      (coherentDiagramTop_max (n + 1 + m)) (by simp; omega) = 0 := by
    rw [he]
    exact SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _
      (fun hi => hβ (fun a b hab => hi (Finset.mem_univ _) (Finset.mem_univ _) hab))
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  unfold dgCoherentBarCoconeLiftColumn
  rw [hz, dgCoherentBarGradedTransport_zero]

lemma dgCoherentBarCoconeLiftColumn_degenerate {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarDegenerateIndex I) :
    dgCoherentBarCoconeLiftColumn R D F c s.val = 0 := by
  rcases s with ⟨⟨n, s⟩, hs⟩
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    rw [I.degenerate_eq_iUnion_range_σ] at hs
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hs
    exact dgCoherentBarCoconeLiftColumn_degeneracy R D F c t i

end SerrePositivity.InfinityCategories
