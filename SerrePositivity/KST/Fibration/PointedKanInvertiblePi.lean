module
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyCategoryComparison
public import SerrePositivity.KST.Spectra.ComponentHomotopyMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-! # 点つき Kan の同じ coherent 可逆辺は、元の基点で全 π を同型にする -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

/-- coherent な逆を元の点つき射へ戻す。両合成の元の成分も恒等射に一致する。 -/
theorem pointedKan_inverse_components {X Y : PointedKanObject.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) :
    ∃ g : Y ⟶ X,
      PointedMapping.componentOf (f.hom ≫ g.hom) = PointedMapping.componentOf (𝟙 X.obj) ∧
      PointedMapping.componentOf (g.hom ≫ f.hom) = PointedMapping.componentOf (𝟙 Y.obj) := by
  have : IsIso (pointedKanHomotopyClass f) := hf
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (inv (pointedKanHomotopyClass f))
  let g : Y ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (SSet.Edge.ofTruncated e)
  have hg : pointedKanHomotopyClass g = inv (pointedKanHomotopyClass f) := by
    dsimp only [pointedKanHomotopyClass, g]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom]
    exact he
  refine ⟨g, ?_, ?_⟩
  · apply (pointedKanHomotopyClass_eq_iff (f ≫ g) (𝟙 X)).mp
    rw [← pointedKanHomotopyClass_comp, hg, pointedKanHomotopyClass_id]
    exact IsIso.hom_inv_id _
  · apply (pointedKanHomotopyClass_eq_iff (g ≫ f) (𝟙 Y)).mp
    rw [← pointedKanHomotopyClass_comp, hg, pointedKanHomotopyClass_id]
    exact IsIso.inv_hom_id _

/-- 元の指定基点での零次を含む全 π 写像は、同じ coherent 可逆性から全単射。 -/
theorem pointedKan_pi_bijective_of_invertible {X Y : PointedKanObject.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n f.hom) := by
  obtain ⟨g, hfg, hgf⟩ := pointedKan_inverse_components f hf
  have hleft : Function.LeftInverse (pointedHomotopyMap n g.hom)
      (pointedHomotopyMap n f.hom) := by
    intro a
    rw [← pointedHomotopyMap_comp,
      pointedHomotopyMap_eq_of_component hfg, pointedHomotopyMap_id]
  have hright : Function.RightInverse (pointedHomotopyMap n g.hom)
      (pointedHomotopyMap n f.hom) := by
    intro a
    rw [← pointedHomotopyMap_comp,
      pointedHomotopyMap_eq_of_component hgf, pointedHomotopyMap_id]
  exact ⟨hleft.injective, hright.surjective⟩

end SerrePositivity.KST.Fibration
