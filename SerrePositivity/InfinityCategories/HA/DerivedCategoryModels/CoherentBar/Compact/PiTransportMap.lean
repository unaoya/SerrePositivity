module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：道を境界に指定した π の基点移送は、元の空間の射で後合成できる。
方針：球面代表と円柱を同じ実射で後合成し、境界の道も同じ射で送る。
規約：基点の移動を忘れず、指定道の像を使う。
使われ方：実加法模型と native 評価空間の比較による移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

lemma dgBarCompactPiTransport_map {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (q : X ⟶ Y) {x y : X _⦋0⦌} (e : X.Edge x y)
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n (e.map q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n q x a) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n q y b) := by
  obtain ⟨f, g, hf, hg, H, hH⟩ := h
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex q rfl f, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex q rfl g, ?_, ?_,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk f) = _
    rw [hf]
    rfl
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map q rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk g) = _
    rw [hg]
    rfl
  · change ((SSet.boundary (n + 1)).ι ▷ Δ[1]) ≫ (H.h ≫ q) = _
    rw [← Category.assoc, hH, Category.assoc]
    congr 1
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
