module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinateNaturality
/-!
概要：任意の native 余錐の高次成分は退化した元の単体で零になる。
方針：末端を保つ拡張の非単射性と、dg nerve の引き戻しの零分岐を使う。
規約：普遍性や正規化模型との比較を仮定しない。
使われ方：任意余錐の成分を正規化 Hom の列へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgCoherentBarExtend_not_injective {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : ¬Function.Injective α) :
    ¬Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  intro hi
  apply hα
  intro a b hab
  apply Fin.castSucc_injective _
  apply hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, hab]

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarGradedTransport_zero {M N M' N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {k l : ℤ}
    (hx : M = M') (hy : N = N') (hk : k = l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) hx hy hk
      (0 : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X k) = 0 := by
  cases hx
  cases hy
  cases hk
  rfl

lemma dgCoherentBarCoconeColumn_degeneracy (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ}
    (s : I _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeColumn R D F c ⟨n + 1, I.σ i s⟩ = 0 := by
  have hn : ¬Function.Injective i.predAboveOrderHom := by
    intro hi
    have hcard := Fintype.card_le_of_injective i.predAboveOrderHom hi
    simp only [Fintype.card_fin] at hcard
    omega
  have hβ := dgCoherentBarExtend_not_injective i.predAboveOrderHom hn
  have he := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_map R D F c s i.predAboveOrderHom
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c (I.σ i s) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c s).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom i.predAboveOrderHom) at he
  have hz : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c (I.σ i s)).hom
      Finset.univ 0 (Fin.last (n + 2)) (-((n + 1 : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + 1)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + 1)) (by simp; omega) = 0 := by
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _
      (fun hi => hβ (fun a b hab => hi (Finset.mem_univ _) (Finset.mem_univ _) hab))
      (by simp)
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeColumn
  rw [hz, dgCoherentBarGradedTransport_zero]

lemma dgCoherentBarCoconeColumn_degenerate (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeColumn R D F c s.val = 0 := by
  rcases s with ⟨⟨n, s⟩, hs⟩
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    rw [I.degenerate_eq_iUnion_range_σ] at hs
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hs
    exact dgCoherentBarCoconeColumn_degeneracy R D F c t i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
