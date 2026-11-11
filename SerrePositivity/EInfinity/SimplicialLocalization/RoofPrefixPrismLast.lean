module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismFront
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeTransport

/-!
# 混合 coherent 錐の元の最後への Hom

概要：時刻零の始点では元の prefix path Hom、時刻一では同じ native roof 全族を使う。
方針：元の通常円柱の対象と同じ端点へ等号で輸送する。
規約：元の全 path・時間・Kan Hom を保持する。
使われ方：native roof 全三角形の mixed coherent 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open Hammock SerrePositivity.InfinityCategories

open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def lastHom {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) :
    SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ⟶
      SimplicialCategory.sHom ((frontDiagram C U p Γ t).obj i)
        ((kanHammockSourceFunctor C).obj Y) := by
  by_cases hi : t i = 0
  · exact pathMap C U p hp σ hU Γ t i ≫ eqToHom (congrArg
      (fun A => SimplicialCategory.sHom A ((kanHammockSourceFunctor C).obj Y))
      (frontDiagram_obj_zero C U p Γ t i hi).symm)
  · have hi1 : t i = 1 := by omega
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm Γ ≫ familyMap C U p hp σ hU) ≫
      eqToHom (congrArg (fun A => SimplicialCategory.sHom A
        ((kanHammockSourceFunctor C).obj Y)) (frontDiagram_obj_one C U p Γ t i hi1).symm)

lemma lastHom_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 0) :
    lastHom C U p hp σ hU Γ t i ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (frontDiagram_obj_zero C U p Γ t i hi) (rfl : (kanHammockSourceFunctor C).obj Y = _)) =
        pathMap C U p hp σ hU Γ t i := by
  simp only [lastHom, dite_eq_left hi, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

lemma lastHom_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 1) :
    lastHom C U p hp σ hU Γ t i ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (frontDiagram_obj_one C U p Γ t i hi) (rfl : (kanHammockSourceFunctor C).obj Y = _)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm Γ ≫ familyMap C U p hp σ hU := by
  have hi0 : t i ≠ 0 := by omega
  simp only [lastHom, dite_eq_right hi0, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
