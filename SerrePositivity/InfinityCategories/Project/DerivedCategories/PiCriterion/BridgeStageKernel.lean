module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PairPathEquality

/-!
概要：D の正次数の後続段階での同一視を、段階に自然な Kan 標的へ反映する。
方針：D の同じ transition による等式を後合成し、脚の Homotopy で戻す。
規約：D の抽象構造を直接消費する。群の余極限は構成しない。
使われ方：全空間比較の正次数の単射性。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- D が後続段階で同一視する二つの類は、段階にホモトピーまで自然な標的でも等しい。 -/
lemma bridge_stage_positive_kernel {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj)
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (n : ℕ) (i : I) (y : (X i).obj _⦋0⦌)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X i).obj n y)
    (hab : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l i) y a = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (l i) y b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s i) rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s i) rfl b := by
  obtain ⟨j, hij, hj⟩ := h.positive_equal_at_stage n i y a b hab
  obtain ⟨H⟩ := hstage i j hij
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.homotopy_map_equality_iff H n y a b).mpr
  have hm (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X i).obj n y) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (τ hij ≫ s j) rfl c =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s j) rfl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (τ hij) y c) :=
    DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (τ hij) rfl (s j) rfl rfl) c
  exact (hm a).trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (s j) rfl) hj).trans (hm b).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
