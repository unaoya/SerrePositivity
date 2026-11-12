module

public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionFaces

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

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory Opposite
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：元の自由な列とその合成の一文字の列を結ぶ実際の辺（Dwyer–Kan）。
方針：列の外側の一文字の一次単体の二面を計算する。
規約：辺の向きは合成の一文字から元の列へ向かう。
使われ方：π₀ の生成関係の証明。 -/
def localizationResolutionWordEdge {X Y : C.category}
    (p : (Paths.of C.category).obj X ⟶ (Paths.of C.category).obj Y) :
    (localizationHom C X Y).Edge (localizationArrowZero C (composePath p))
      (localizationResolutionHom C 0 p) :=
  .mk (localizationResolutionHom C 1 ((Paths.of (Paths C.category)).map p))
    (by
      rw [localizationResolutionHom_delta_one]
      simp only [Cat.freeMap_map, Paths.of_map, Prefunctor.mapPath_toPath,
        Functor.toPrefunctor_map, pathComposition_map]
      exact localizationResolutionHom_zero_arrow C (composePath p))
    (by
      rw [localizationResolutionHom_delta_zero]
      simp only [Paths.of_map, pathComposition_map, composePath_toPath])

/-- 概要：自由な列の類はその合成の一文字の射の類（Dwyer–Kan）。
方針：同じ一次の辺に π₀ の商関係を適用する。
規約：元の列を変更しない。
使われ方：恒等・合成と列の帰納。 -/
lemma localizationResolutionWordClass {X Y : C.category}
    (p : (Paths.of C.category).obj X ⟶ (Paths.of C.category).obj Y) :
    localizationArrowClass C (composePath p) =
      SSet.π₀.mk (localizationResolutionHom C 0 p) :=
  SSet.π₀.sound (localizationResolutionWordEdge C p)

/-- 概要：元の恒等射の類は連結成分の圏の恒等射（Dwyer–Kan）。
方針：空列の一次の辺と標準表示の恒等則を使う。
規約：元の恒等射を保持する。
使われ方：元の圏から連結成分の圏への関手の単位則。 -/
lemma localizationArrowClass_id (X : C.category) :
    localizationArrowClass C (𝟙 X) = 𝟙 (show LocalizationComponents C from X) := by
  have h := localizationResolutionWordClass C (𝟙 ((Paths.of C.category).obj X))
  change localizationArrowClass C (𝟙 X) =
    SSet.π₀.mk (localizationResolutionHom C 0 (𝟙 (freeResolutionGeneratorObject C 1 X))) at h
  rw [localizationResolutionHom_id] at h
  exact h

/-- 概要：元の合成の類は連結成分の圏での合成（Dwyer–Kan）。
方針：二文字の列の一次の辺と標準表示の合成則を使う。
規約：元の相対圏の合成順序を保持する。
使われ方：元の圏から連結成分の圏への関手の合成則。 -/
lemma localizationArrowClass_comp {X Y Z : C.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    localizationArrowClass C (f ≫ g) = localizationArrowClass C f ≫ localizationArrowClass C g := by
  have h := localizationResolutionWordClass C
    ((Paths.of C.category).map f ≫ (Paths.of C.category).map g)
  have hc : composePath ((Paths.of C.category).map f ≫ (Paths.of C.category).map g) =
      f ≫ g := by simp only [composePath_comp', Paths.of_map, composePath_toPath]
  rw [hc, localizationResolutionHom_comp, localizationResolutionHom_zero_arrow,
    localizationResolutionHom_zero_arrow] at h
  exact h

/-- 概要：元の圏から DK の連結成分の圏への同じ生成関手（Dwyer–Kan）。
方針：一文字の列の類と一次の辺からの恒等・合成則を束ねる。
規約：対象は同じ元の対象。
使われ方：普通の局所化からの逆関手の入力。 -/
def localizationComponentsQ : C.category ⥤ LocalizationComponents C where
  obj X := X
  map := localizationArrowClass C
  map_id := localizationArrowClass_id C
  map_comp := localizationArrowClass_comp C

end SerrePositivity.EInfinity.SimplicialLocalization
