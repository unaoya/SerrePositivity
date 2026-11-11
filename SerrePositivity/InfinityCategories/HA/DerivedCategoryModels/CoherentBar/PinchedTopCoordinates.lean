module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LeftRightHomCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeFullCoefficient
/-!
概要：右 pinched Hom への実単体写像は、全次数の最上成分によって決定される。
方針：昇順部分単体へ制限する自然性により、最上成分から全部分集合を回収する。
規約：各次数の成分は次数 −n の実 dg Hom に取る。
使われ方：固定終点の比較を全部分集合の添字輸送なしで照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)

def dgCoherentBarPinchedTop {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component Finset.univ (-(n : ℤ)) Finset.univ_nonempty (by simp)

lemma dgCoherentBarPinchedTop_hom_heq {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌) :
    HEq (dgCoherentBarPinchedTop R C x y s)
      (s.val.hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n) (by simp; omega)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq s Finset.univ (-(n : ℤ))
    Finset.univ_nonempty (by simp)
  have hMin : (Finset.univ : Finset (Fin (n + 1))).min' Finset.univ_nonempty = 0 :=
    le_antisymm (Finset.min'_le _ _ (Finset.mem_univ 0)) (Fin.zero_le _)
  refine h.trans ?_
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree s.val.toSimplexData
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ n) (by rw [hMin]; rfl) rfl rfl

lemma dgCoherentBarPinched_hom_ext_of_top {K : SSet.{max u v}}
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y)
    (h : ∀ (n : ℕ) (s : K _⦋n⦌), dgCoherentBarPinchedTop R C x y (f.app _ s) =
      dgCoherentBarPinchedTop R C x y (g.app _ s)) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).injective
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change J.Nonempty at hJ
  change k = 1 - (J.card : ℤ) at hk
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (f.app (Opposite.op ⦋n⦌) s)).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (g.app (Opposite.op ⦋n⦌) s)).component J k hJ hk
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp [r]; omega
  have hkr : k = -(r : ℤ) := by rw [hc] at hk; push_cast at hk; omega
  cases hkr
  let β := SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom
  have hTop := h r (K.map β.op s)
  rw [f.naturality_apply β.op s, g.naturality_apply β.op s] at hTop
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((f.app (Opposite.op ⦋n⦌) s).pullback β)).component
    Finset.univ (-(r : ℤ)) Finset.univ_nonempty (by simp) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((g.app (Opposite.op ⦋n⦌) s).pullback β)).component
      Finset.univ (-(r : ℤ)) Finset.univ_nonempty (by simp) at hTop
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_pullback,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ (J.orderEmbOfFin hc).injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ (J.orderEmbOfFin hc).injective.injOn] at hTop
  have hImg : (Finset.univ : Finset (Fin (r + 1))).image β.toOrderHom = J :=
    J.image_orderEmbOfFin_univ hc
  simpa only [hImg] using hTop

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
