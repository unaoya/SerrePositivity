module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionRepresentatives

/-!
# 自由単体的局所化の一次の二面

概要：Dwyer–Kan の標準射の一次単体の二面を元の自由圏の射で計算する。
方針：各面の厳密な局所化の因子化を Hom に評価し、対象移送を相殺する。
規約：一次の外側合成と内側合成を区別して保持する。
使われ方：元の射の連結成分の恒等・合成則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：一次の外側の面は同じ列の外側合成を与える（Dwyer–Kan）。
方針：外側の余単位の局所化の因子化で対象移送を相殺する。
規約：元の一次単体を保持する。
使われ方：一文字の列の辺の終点。 -/
lemma localizationResolutionHom_delta_zero {X Y : C.category}
    (f : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C 2 X ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C 2 Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).δ 0 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 1 f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 0 ((pathComposition (Paths C.category)).map f) := by
  have hF : C.weakEquivalences.paths.paths.Q ⋙
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (0 : Fin 2)).toFunctor =
    pathComposition (Paths C.category) ⋙ C.weakEquivalences.paths.Q := by
    change C.weakEquivalences.paths.paths.Q ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).δ (0 : Fin 2)) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution_face]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences.paths)
  have h := Functor.congr_hom hF f
  simp only [Functor.comp_map] at h
  change eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (0 : Fin 2)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 1 f) ≫ eqToHom _ = _
  change eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (0 : Fin 2)).toFunctor.map
      (eqToHom _ ≫ C.weakEquivalences.paths.paths.Q.map f ≫ eqToHom _) ≫ eqToHom _ =
    eqToHom _ ≫ C.weakEquivalences.paths.Q.map
      ((pathComposition (Paths C.category)).map f) ≫ eqToHom _
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- 概要：一次の内側の面は列の各射を合成した列を与える（Dwyer–Kan）。
方針：余単位の自由像の局所化の因子化で対象移送を相殺する。
規約：外側の列の順序を変更しない。
使われ方：一文字の列の辺の始点。 -/
lemma localizationResolutionHom_delta_one {X Y : C.category}
    (f : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C 2 X ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C 2 Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).δ 1 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 1 f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 0
        ((Cat.freeMap (pathComposition C.category).toPrefunctor).map f) := by
  have hF : C.weakEquivalences.paths.paths.Q ⋙
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (1 : Fin 2)).toFunctor =
    Cat.freeMap (pathComposition C.category).toPrefunctor ⋙ C.weakEquivalences.paths.Q := by
    change C.weakEquivalences.paths.paths.Q ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).δ (1 : Fin 2)) = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution_face]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences))
  have h := Functor.congr_hom hF f
  simp only [Functor.comp_map] at h
  change eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (1 : Fin 2)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 1 f) ≫ eqToHom _ = _
  change eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolution C).δ (1 : Fin 2)).toFunctor.map
      (eqToHom _ ≫ C.weakEquivalences.paths.paths.Q.map f ≫ eqToHom _) ≫ eqToHom _ =
    eqToHom _ ≫ C.weakEquivalences.paths.Q.map
      ((Cat.freeMap (pathComposition C.category).toPrefunctor).map f) ≫ eqToHom _
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
