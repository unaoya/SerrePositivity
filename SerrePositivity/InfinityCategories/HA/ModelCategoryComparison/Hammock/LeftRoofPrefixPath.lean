module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PathMaximumCylinderEndpoints
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrefixNaturality

/-!
# 最大座標で元の prefix 円柱を評価した全 Hom 写像

概要：path の最後の最大座標と時間を同じ Under 円柱に代入する。
方針：元の全円柱の自然性と最大座標の全整合性を合成する。
規約：元の hammock 余極限・全 path パラメータ・全単体作用素を保持する。
使われ方：native roof prism の 00 合成と両端の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory _root_.SSet _root_.CategoryTheory.SimplicialThickening
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative]
  (U : I ⥤ C) {X Y : C} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, W (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a))

def pathMap {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LastPath.{u} n i) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W (U.obj (Γ.obj i)) Y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates Γ t i ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy W U p hp σ hU (Γ.obj i)).h

lemma pathMap_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU Γ t (α.toOrderHom i) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) i := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates_reindex]
  rfl

lemma pathMap_comp {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU Γ t i =
    snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU Γ t j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (U.map (Γ.map (homOfLE hij)))) Y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates_comp Γ t i j hij]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy_underMap W U p hp σ hU (Γ.obj i) (Γ.map (homOfLE hij))]

lemma pathMap_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU Γ (OrderHom.const _ 0) i =
      toUnit _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (σ.app (Γ.obj i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates_zero, Category.assoc,
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy W U p hp σ hU (Γ.obj i)).h₀, ← Category.assoc, comp_toUnit]

lemma pathMap_one_of_source {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 1) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap W U p hp σ hU Γ t i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm Γ ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W U p hp σ hU) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app (Γ.obj i))) Y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.pathMap]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates_one_of_source Γ t i hi, Category.assoc,
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy W U p hp σ hU (Γ.obj i)).h₁, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap_eq_precomp]
  simp only [Category.assoc]
  rw [← Category.assoc (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i))
    (nerveMap (Under.forget (Γ.obj i))), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor_nerve_forget]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
