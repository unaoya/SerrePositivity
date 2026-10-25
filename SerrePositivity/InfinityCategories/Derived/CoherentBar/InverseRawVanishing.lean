module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawPartialNaturality
/-!
概要：左右いずれかの添字が退化する混合成分は、逆構成でも零になる。
方針：パラメーター係数の退化消滅または元の部分単体の native 列の消滅を使う。
規約：零成分の端点と次数の輸送を明示する。
使われ方：逆構成の全退化写像に対する自然性。
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

lemma dgCoherentBarInverseRawData_mixed_zero_of_column {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty) (r : ℕ) (hcK : K.card = r + 1)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (ha : a = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hb : b = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ))
    (hCol : dgCoherentBarInverseMixedColumn R D F hMC N f L (1 - (L.card : ℤ)) hL rfl
      (dgCoherentBarSubsetLabel s K r hcK) = 0) :
    (dgCoherentBarInverseRawData R D F hMC N f s).hom
      (dgCoherentBarJoinSubset K L) a b k hJ ha hb hk = 0 := by
  have hRaw := dgCoherentBarInverseRawData_mixed_hom_heq R D F hMC N f s
    K L hK hL r hcK (1 - (L.card : ℤ)) rfl a b k hJ ha hb hk
  rw [hCol] at hRaw
  have hx : (dgCoherentBarInverseRawData R D F hMC N f s).obj a =
      dgCoherentBarSource R D F (dgCoherentBarSubsetLabel s K r hcK) := by
    rw [ha, dgCoherentBarJoinSubset_min K L hK (Index.nonempty hJ)]
    have h := congrArg (fun t : SimplexData R (RightModule R D) n => t.obj (K.min' hK))
      (dgCoherentBarInverseRawData_left R D F hMC N f s)
    exact h.trans (dgCoherentBarSubsetLabel_source R D F s K r hcK hK).symm
  have hz : (dgCoherentBarInverseRawData R D F hMC N f s).obj b = N := by
    rw [hb, dgCoherentBarJoinSubset_max K L hL (Index.nonempty hJ)]
    have h := congrArg (fun t : SimplexData R (RightModule R D) m => t.obj (L.max' hL))
      (dgCoherentBarInverseRawData_right R D F hMC N f s)
    exact h
  have hdeg : k = 1 - (L.card : ℤ) - (r : ℤ) := by
    rw [dgCoherentBarJoinSubset_card, hcK] at hk
    push_cast at hk
    omega
  exact eq_of_heq (hRaw.trans
    (gradedHom_zero_heq (A := R) (D := RightModule R D) hx hz hdeg).symm)

lemma dgCoherentBarInverseRawData_mixed_zero_of_not_injOn {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (hi : ¬ Set.InjOn (dgCoherentBarJoinOrderMap α β)
      ((dgCoherentBarJoinSubset K L) : Set (Fin (a + b + 1 + 1))))
    (c d : Fin (a + b + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (dgCoherentBarJoinSubset K L).card)
    (hc : c = (dgCoherentBarJoinSubset K L).min' (Index.nonempty hJ))
    (hd : d = (dgCoherentBarJoinSubset K L).max' (Index.nonempty hJ))
    (hk : k = 2 - ((dgCoherentBarJoinSubset K L).card : ℤ)) :
    (dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).hom
      (dgCoherentBarJoinSubset K L) c d k hJ hc hd hk = 0 := by
  classical
  let r := K.card - 1
  have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  apply dgCoherentBarInverseRawData_mixed_zero_of_column R D F hMC N _ _ K L hK hL
    r hcK c d k hJ hc hd hk
  have hNot : ¬ (Set.InjOn α (K : Set (Fin (a + 1))) ∧
      Set.InjOn β (L : Set (Fin (b + 1)))) := by
    intro h
    exact hi ((dgCoherentBarJoinOrderMap_injOn_subset_iff α β K L).mpr h)
  rcases not_and_or.mp hNot with hα | hβ
  · have hDeg := dgCoherentBarSubsetLabel_degenerate_of_not_injOn s α K hα r hcK
    exact dgCoherentBarInverseMixedColumn_source_degenerate R D F hMC N
      (DGNerve.PinchedHom.LinearData.pullback β f) L (1 - (L.card : ℤ)) hL rfl
      ⟨dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op s) K r hcK, hDeg⟩
  · unfold dgCoherentBarInverseMixedColumn
    rw [dgCoherentBarInverseParameterCoefficient_pullback_not_inj f β L
      (1 - (L.card : ℤ)) hL rfl hβ, DGNerve.zero_compose]

end SerrePositivity.InfinityCategories
