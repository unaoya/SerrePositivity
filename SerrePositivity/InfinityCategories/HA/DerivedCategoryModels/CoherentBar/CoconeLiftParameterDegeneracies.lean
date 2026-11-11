module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftDegeneracies
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarCoconeLiftColumn_parameter_degeneracy {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftColumn R D F ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).σ i c) s = 0 := by
  rcases s with ⟨n, s⟩
  have hn : ¬Function.Injective i.predAboveOrderHom := by
    intro hi
    have hc := Fintype.card_le_of_injective i.predAboveOrderHom hi
    simp only [Fintype.card_fin] at hc
    omega
  have hβ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_not_injective_right
    (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) i.predAboveOrderHom hn
  have he := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_map R D F c s
    (𝟙 ⦋n⦌) (SimplexCategory.σ i)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at he
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).σ i c) s =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap OrderHom.id i.predAboveOrderHom) at he
  have hz : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).σ i c) s).hom
      Finset.univ 0 (Fin.last (n + (m + 1) + 1)) (-((m + 1 : ℕ) : ℤ) - (n : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + (m + 1))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + (m + 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + (m + 1))) (by simp; omega) = 0 := by
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _
      (fun hi => hβ (fun a b hab => hi (Finset.mem_univ _) (Finset.mem_univ _) hab))
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftColumn
  rw [hz, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarGradedTransport_zero]

lemma dgCoherentBarCoconeLiftHom_parameter_degeneracy
    (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).σ i c) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).σ i c)) (-((m + 1 : ℕ) : ℤ))).injective
  rw [map_zero]
  funext s
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom, LinearEquiv.apply_symm_apply, Pi.zero_apply]
  exact dgCoherentBarCoconeLiftColumn_parameter_degeneracy R D F c s.val i

lemma dgCoherentBarCoconeLiftHom_heq_of_index_eq
    (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (c' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌)
    (h : (⟨m, c⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)) = ⟨n, c'⟩) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c') := by
  cases h
  rfl

lemma dgCoherentBarCoconeLiftHom_degenerate
    (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
    (a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC a.val.2 = 0 := by
  rcases a with ⟨⟨n, c⟩, hc⟩
  cases n with
  | zero => simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hc
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ] at hc
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.mp hc
    exact dgCoherentBarCoconeLiftHom_parameter_degeneracy R D F hMC c i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
