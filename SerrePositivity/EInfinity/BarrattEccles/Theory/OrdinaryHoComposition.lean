module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.EdgeHom

/-!
# 通常の nerve とホモトピー圏の関手性

## 概要
Kerodon §1.4.6（Tag 004Q） のホモトピー圏関手の合成と、通常の圏からの包含を比較する。

## 方針
単体集合の関手性と、nerve の辺の端点・一次単体の公式を使う。

## 規約
通常の圏の射の宇宙と対象の宇宙を区別する。

## 使われ方
厳密な H⁰ の比較を CAlg のホモトピー圏に降ろす。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 単体集合の射の合成は、誘導されるホモトピー圏の関手の合成と自然同型。 -/
def hoMapCompIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hoMap (f ≫ g) ≅ hoMap f ⋙ hoMap g := by
  apply eqToIso
  change (hoFunctor.map (f ≫ g)).toFunctor = _
  rw [hoFunctor.map_comp]
  rfl

/-- 通常の圏から nerve のホモトピー圏への包含は、通常の関手について自然。 -/
def ordinaryToHoNerve_naturalIso {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] (F : C ⥤ D) :
    ordinaryToHoNerve C ⋙ hoMap (nerveMap F) ≅ F ⋙ ordinaryToHoNerve D := by
  refine NatIso.ofComponents (fun X =>
    eqToIso (congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F X))) ?_
  intro X Y g
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.homMk_congr (nerveMap_app_mk₀ F X) (nerveMap_app_mk₀ F Y)
    ((nerve.edgeMk g).map (nerveMap F)) (nerve.edgeMk (F.map g)) (nerveMap_app_mk₁ F g)
  let hx := congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F X)
  let hy := congrArg HomotopyCategory.mk (nerveMap_app_mk₀ F Y)
  change HomotopyCategory.homMk ((nerve.edgeMk g).map (nerveMap F)) ≫ eqToHom hy =
    eqToHom hx ≫ HomotopyCategory.homMk (nerve.edgeMk (F.map g))
  rw [← h]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

end SerrePositivity.EInfinity
