module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismLast

/-!
# 混合 coherent 錐の最後 Hom の元の合成条件

概要：通常の評価円柱の射と時刻で切り替えた最後 Hom の全合成を照合する。
方針：00・01 は元の path 合成式、11 は最大座標の合成則と豊穣単位を使う。
規約：元の全時間・全 path・全 Kan Hom を保持する。
使われ方：native roof の混合 coherent 図式の EnrichedFunctor 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.EInfinity.Hammock _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma lastHom_comp {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom C U p hp σ hU Γ t i =
    lift (toUnit _ ≫ eHomEquiv SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).map (homOfLE hij)))
      (snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom C U p hp σ hU Γ t j) ≫
        eComp SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).obj i) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).obj j)
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lift_const_tensor]
  by_cases hi : t i = 0
  · by_cases hj : t j = 0
    · let hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_zero C U p Γ t i hi
      let hJ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_zero C U p Γ t j hj
      have hf := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitHom_transport hI hJ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).map (homOfLE hij))
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map (U.map (Γ.map (homOfLE hij))))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_map_zero_zero C U p Γ t i j hij hi hj)
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized hI hJ rfl _ _ _ _).2
      simp only [Category.assoc, hf]
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_zero C U p hp σ hU Γ t i hi,
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_zero C U p hp σ hU Γ t j hj]
      have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.pathMap_comp_enriched C U p hp σ hU Γ t i j hij
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lift_const_tensor] at h
      exact h
    · have hj1 : t j = 1 := by omega
      let hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_zero C U p Γ t i hi
      let hJ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_one C U p Γ t j hj1
      have hf := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitHom_transport hI hJ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).map (homOfLE hij))
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map (p.app (Γ.obj i)))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_map_zero_one C U p Γ t i j hij hi hj1)
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized hI hJ rfl _ _ _ _).2
      simp only [Category.assoc, hf]
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_zero C U p hp σ hU Γ t i hi,
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_one C U p hp σ hU Γ t j hj1]
      have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.pathMap_comp_one_enriched C U p hp σ hU Γ t i j hij hj1
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.lift_const_tensor] at h
      exact h
  · have hi1 : t i = 1 := by omega
    have hj1 : t j = 1 := by
      have h := t.monotone hij
      rw [hi1] at h
      exact le_antisymm (Fin.le_last _) h
    let hI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_one C U p Γ t i hi1
    let hJ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_obj_one C U p Γ t j hj1
    have hf := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitHom_transport hI hJ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram C U p Γ t).map (homOfLE hij))
      (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.frontDiagram_map_one_one C U p Γ t i j hij hi1 hj1)
    simp only [eHomEquiv_id] at hf
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized hI hJ rfl _ _ _ _).2
    simp only [Category.assoc, hf]
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_one C U p hp σ hU Γ t i hi1,
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.lastHom_one C U p hp σ hU Γ t j hj1]
    let M : (Δ[n] : SSet.{u}) ⟶ SimplicialCategory.sHom
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y) :=
      SSet.yonedaEquiv.symm Γ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.familyMap C U p hp σ hU
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change M.app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d
      ((eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j.castSucc)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1)))).app d (P, Q))) =
      (eComp SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y)).app d
        ((eId SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)).app d PUnit.unit,
          M.app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j).app d Q))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLastMaximumMap_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y) d _).symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix
