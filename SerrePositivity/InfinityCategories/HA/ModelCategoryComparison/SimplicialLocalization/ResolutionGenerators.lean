module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentCategory

/-!
# 自由単体的局所化の元の射の零単体

概要：Dwyer–Kan の自由解像の零次に元の圏の射を一文字の列として送る。
方針：同じ augmentation の対象単射性で標準生成対象と固定対象表示を同定する。
規約：零次の生成写像自体には合成保存を仮定しない。
使われ方：連結成分の圏と普通の局所化との比較の逆写像。
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

/-- 概要：零次の固定対象表示は自由圏の元の生成対象（Dwyer–Kan）。
方針：同じ augmentation の対象単射性と厳密な局所化の因子化を使う。
規約：元の自由圏の対象を保持する。
使われ方：一文字の射を零単体へ移す対象の同定。 -/
lemma localizedFreeResolutionObject_zero (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C (op ⦋0⦌) X =
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObjectEquiv C (op ⦋0⦌)).injective
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation C).app (op ⦋0⦌)).toFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject C (op ⦋0⦌) X) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).obj
      (C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object]
  exact (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences))
    ((Paths.of C.category).obj X)).symm

/-- 概要：元の射の一文字の列を同じ DK Hom の零単体へ送る（Dwyer–Kan）。
方針：元の自由局所化の生成射を対象表示の同じ等式で移す。
規約：零単体での合成保存は要求しない。
使われ方：元の射の連結成分の供給。 -/
def localizationArrowZero {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) _⦋0⦌ :=
  eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_zero C X) ≫
    C.weakEquivalences.paths.Q.map ((Paths.of C.category).map f) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_zero C Y).symm

/-- 概要：元の射は同じ DK Hom の連結成分を定める（Dwyer–Kan）。
方針：元の一文字の列の零単体の類を取る。
規約：合成保存は一次の自由解像の辺から後続で証明する。
使われ方：普通の局所化との比較の生成射の逆像。 -/
def localizationArrowClass {X Y : C.category} (f : X ⟶ Y) :
    (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C from X) ⟶ (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C from Y) :=
  SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero C f)

/-- 概要：元の一文字の零単体の比較は元の射の局所化像（Dwyer–Kan）。
方針：同じ augmentation の厳密な因子化を Hom に評価して対象移送を相殺する。
規約：元の局所化関手 Q と元の生成射を保持する。
使われ方：π₀ 比較の元の射に関する正規化。 -/
lemma localizationHomAugmentation_arrow {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero C f) =
      C.weakEquivalences.Q.map f := by
  have h := Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences))
    ((Paths.of C.category).map f)
  simp only [Functor.comp_map] at h
  change eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object C (op ⦋0⦌) X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero C f) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object C (op ⦋0⦌) Y) = _
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowZero
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [h]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit, pathComposition_map, Paths.of_map, composePath_toPath,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]

/-- 概要：元の射の連結成分の比較は同じ Q の射（Dwyer–Kan）。
方針：零単体の類の比較と一文字の射の正規化を合成する。
規約：元の射を別の代表に置き換えない。
使われ方：普通の局所化への比較の逆写像の検証。 -/
lemma localizationComponentsAugmentation_arrow {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C f) =
      C.weakEquivalences.Q.map f :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation_arrow C f

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
