module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionFaces

/-!
# 自由な列とその合成の一文字の列を結ぶ辺

概要：Dwyer–Kan の一次の自由解像が与える元の列の関係を辺として構成する。
方針：内側の列を外側の一文字にし、二つの面の既存の式を使う。
規約：元の列・元の合成・元の局所化を保持する。
使われ方：元の射の類の恒等・合成保存と普通の局所化の逆関手。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.Opposite
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：元の自由な列とその合成の一文字の列を結ぶ実際の辺（Dwyer–Kan）。
方針：列の外側の一文字の一次単体の二面を計算する。
規約：辺の向きは合成の一文字から元の列へ向かう。
使われ方：π₀ の生成関係の証明。 -/
def localizationResolutionWordEdge {X Y : C.category}
    (p : (Paths.of C.category).obj X ⟶ (Paths.of C.category).obj Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y).Edge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero C (composePath p))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 0 p) :=
  .mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 1 ((Paths.of (Paths C.category)).map p))
    (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_delta_one]
      simp only [Cat.freeMap_map, Paths.of_map, Prefunctor.mapPath_toPath,
        Functor.toPrefunctor_map, pathComposition_map]
      exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_zero_arrow C (composePath p))
    (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_delta_zero]
      simp only [Paths.of_map, pathComposition_map, composePath_toPath])

/-- 概要：自由な列の類はその合成の一文字の射の類（Dwyer–Kan）。
方針：同じ一次の辺に π₀ の商関係を適用する。
規約：元の列を変更しない。
使われ方：恒等・合成と列の帰納。 -/
lemma localizationResolutionWordClass {X Y : C.category}
    (p : (Paths.of C.category).obj X ⟶ (Paths.of C.category).obj Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C (composePath p) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 0 p) :=
  SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionWordEdge C p)

/-- 概要：元の恒等射の類は連結成分の圏の恒等射（Dwyer–Kan）。
方針：空列の一次の辺と標準表示の恒等則を使う。
規約：元の恒等射を保持する。
使われ方：元の圏から連結成分の圏への関手の単位則。 -/
lemma localizationArrowClass_id (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C (𝟙 X) = 𝟙 (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C from X) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionWordClass C (𝟙 ((Paths.of C.category).obj X))
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C (𝟙 X) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom C 0 (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C 1 X))) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_id] at h
  exact h

/-- 概要：元の合成の類は連結成分の圏での合成（Dwyer–Kan）。
方針：二文字の列の一次の辺と標準表示の合成則を使う。
規約：元の相対圏の合成順序を保持する。
使われ方：元の圏から連結成分の圏への関手の合成則。 -/
lemma localizationArrowClass_comp {X Y Z : C.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C (f ≫ g) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C g := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionWordClass C
    ((Paths.of C.category).map f ≫ (Paths.of C.category).map g)
  have hc : composePath ((Paths.of C.category).map f ≫ (Paths.of C.category).map g) =
      f ≫ g := by simp only [composePath_comp', Paths.of_map, composePath_toPath]
  rw [hc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_comp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_zero_arrow,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationResolutionHom_zero_arrow] at h
  exact h

/-- 概要：元の圏から DK の連結成分の圏への同じ生成関手（Dwyer–Kan）。
方針：一文字の列の類と一次の辺からの恒等・合成則を束ねる。
規約：対象は同じ元の対象。
使われ方：普通の局所化からの逆関手の入力。 -/
def localizationComponentsQ : C.category ⥤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C where
  obj X := X
  map := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C
  map_id := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass_id C
  map_comp := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass_comp C

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
