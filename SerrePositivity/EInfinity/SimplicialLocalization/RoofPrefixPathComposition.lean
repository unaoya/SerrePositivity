module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPath
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockPrecompose
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ArrowMapComposition

/-!
# 元の prefix path 写像の実 Kan 豊穣合成則

概要：元の通常射と prefix path の合成、および時刻一への切替を同じ豊穣合成で計算する。
方針：元の augmentation の自然性と Ex∞ の前合成・豊穣合成の厳密な一致を使う。
規約：全 path・時間・通常射・元の Kan Hom を保持する。
使われ方：native roof prism の 00 と 01 合成条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet SimplicialThickening
open Hammock SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma pathMap_comp_enriched {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ pathMap C U p hp σ hU Γ t i =
    lift (toUnit _ ≫ ForgetEnrichment.homTo SSet.{u}
      ((kanHammockSourceFunctor C).map (U.map (Γ.map (homOfLE hij)))))
      (snd _ _ ≫ pathMap C U p hp σ hU Γ t j) ≫
        eComp SSet ((kanHammockSourceFunctor C).obj (U.obj (Γ.obj i)))
          ((kanHammockSourceFunctor C).obj (U.obj (Γ.obj j)))
          ((kanHammockSourceFunctor C).obj Y) := by
  rw [pathMap_comp C U p hp σ hU Γ t i j hij, ← Category.assoc]
  exact kanHammockSource_precompose_family C (U.map (Γ.map (homOfLE hij))) Y _

lemma pathMap_comp_one_of_target {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j) (hj : t j = 1) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ pathMap C U p hp σ hU Γ t i =
    snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j ≫ SSet.yonedaEquiv.symm Γ ≫ familyMap C U p hp σ hU ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences (p.app (Γ.obj i))) Y) := by
  rw [pathMap_comp C U p hp σ hU Γ t i j hij,
    pathMap_one_of_source C U p hp σ hU Γ t j hj]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps_arrowMap]
  have h := (p.naturality (Γ.map (homOfLE hij))).trans (Category.comp_id _)
  rw [h]

lemma pathMap_comp_one_enriched {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j) (hj : t j = 1) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ pathMap C U p hp σ hU Γ t i =
    lift (toUnit _ ≫ ForgetEnrichment.homTo SSet.{u}
      ((kanHammockSourceFunctor C).map (p.app (Γ.obj i))))
      (snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j ≫ SSet.yonedaEquiv.symm Γ ≫ familyMap C U p hp σ hU) ≫
        eComp SSet ((kanHammockSourceFunctor C).obj (U.obj (Γ.obj i)))
          ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y) := by
  rw [pathMap_comp_one_of_target C U p hp σ hU Γ t i j hij hj]
  simp only [← Category.assoc]
  exact kanHammockSource_precompose_family C (p.app (Γ.obj i)) Y _

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
