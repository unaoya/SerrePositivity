module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeDegenerateColumns
/-!
概要：任意の native 余錐の全部分集合成分を、同じ部分単体の最上係数へ戻す。
方針：先頭集合の昇順列挙と末端を加えた単射自然性を使う。
規約：全端点と次数を異種等号で保持する。
使われ方：Hom の逆像が余錐の全 HA 成分を厳密に回収することの検証。
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

lemma dgCoherentBarCoconeSimplex_last_hom_heq (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeColumn R D F c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiLabel s J hJ hb)) := by
  have hl : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J
  have hK : K.Nonempty := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hl
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  let α := (K.orderEmbOfFin hc).toOrderHom
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α
  let τ := I.map (SimplexCategory.mkHom α).op s
  have hβ : Function.Injective β := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarExtend_injective α (K.orderEmbOfFin hc).injective
  have him : (Finset.univ : Finset (Fin (r + 2))).image β = J := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ r, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withLast_extend]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast ((Finset.univ : Finset (Fin (r + 1))).image
      (K.orderEmbOfFin hc)) = J
    rw [K.image_orderEmbOfFin_univ hc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast J hl
  have hA : β 0 = a := by
    rw [ha]
    have h0 : IsLeast ((Finset.univ : Finset (Fin (r + 2))) : Set (Fin (r + 2))) 0 :=
      ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
    simpa only [him] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min β.monotone h0
      (Finset.Nonempty.image Finset.univ_nonempty β)
  have hkr : k = -(r : ℤ) := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast J hl
    change J.card = K.card + 1 at hh
    omega
  have hNat := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_map R D F c s α)
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c τ).toSimplexData =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c s).toSimplexData.pullback β at hNat
  have hHom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq hNat Finset.univ 0 (Fin.last (r + 1))
    (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ.injOn] at hHom
  have hAny : HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c τ).hom
        Finset.univ 0 (Fin.last (r + 1)) (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)) := by
    refine HEq.trans ?_ hHom.symm
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree _ him.symm hA.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α).symm hkr
  refine hAny.trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := R) (D := RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_source R D F c τ)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_last R D F c τ) rfl _).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
