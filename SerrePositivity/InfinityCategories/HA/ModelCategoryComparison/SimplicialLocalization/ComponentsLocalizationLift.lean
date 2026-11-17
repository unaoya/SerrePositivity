module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ZeroLevelComponents

/-!
# 普通の局所化から DK の連結成分の圏への持ち上げ

概要：元の指定弱同値を反転する同じ生成関手を普通の局所化へ延長する。
方針：零次の局所化の可逆性を連結成分へ送り、構成的な lift を使う。
規約：元の局所化と元の生成射の類を保持する。
使われ方：DK Hom の π₀ と普通の局所化 Hom の比較の逆関手。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：元の生成関手は指定弱同値を反転する（Dwyer–Kan）。
方針：一文字の弱同値の零次の局所化の同型を同じ連結成分関手で送る。
規約：元の指定弱同値類を変更しない。
使われ方：普通の局所化への持ち上げの入力。 -/
lemma localizationComponentsQ_inverts :
    C.weakEquivalences.IsInvertedBy (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C) :=
  fun X Y f hf => by
    have hw : C.weakEquivalences.paths ((Paths.of C.category).map f) := ⟨trivial, hf⟩
    have := C.weakEquivalences.paths.Q_inverts _ hw
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.zeroLevelComponentsFunctor C).map_isIso
      (C.weakEquivalences.paths.Q.map ((Paths.of C.category).map f))

/-- 概要：普通の局所化から同じ DK 連結成分の圏への持ち上げ（Dwyer–Kan）。
方針：同じ生成関手と指定弱同値の反転を構成的な lift に渡す。
規約：対象・射の元の類を保持する。
使われ方：π₀ 比較の逆関手。 -/
def localizationComponentsLift : C.weakEquivalences.Localization ⥤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C :=
  Localization.Construction.lift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ_inverts C)

/-- 概要：持ち上げは元の生成関手で厳密に因子化する（Dwyer–Kan）。
方針：同じ構成的な局所化の因子化の等式を使う。
規約：自然同型だけでなく元の関手の等式。
使われ方：比較関手との合成の一意性。 -/
lemma localizationComponentsLift_fac :
    C.weakEquivalences.Q ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C :=
  Localization.Construction.fac _ _

/-- 概要：生成関手を元の augmentation で戻すと同じ Q（Dwyer–Kan）。
方針：元の生成射の Q への正規化を関手の等式に束ねる。
規約：同じ対象・元の射を保持する。
使われ方：普通の局所化上の合成の恒等則。 -/
lemma localizationComponentsQ_comp_augmentation :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C = C.weakEquivalences.Q := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation_arrow C f

/-- 概要：逆向きの持ち上げを augmentation で戻すと恒等（Dwyer–Kan）。
方針：元の局所化の厳密な一意性と生成関手の同じ因子化を使う。
規約：同じ普通の局所化上の関手等式。
使われ方：π₀ 比較の片側の逆則。 -/
lemma localizationComponentsLift_comp_augmentation :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C =
      𝟭 C.weakEquivalences.Localization := by
  apply Localization.Construction.uniq
  rw [← Functor.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift_fac,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ_comp_augmentation, Functor.comp_id]

/-- 概要：零次の局所化の持ち上げは元の同じ連結成分関手（Dwyer–Kan）。
方針：零次の構成的局所化の一意性と自由な列の辺の関係を使う。
規約：元の零次の全射を含む厳密な等式。
使われ方：π₀ 比較の反対側の逆則。 -/
lemma strictLocalizationCounit_comp_componentsLift :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences) ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.zeroLevelComponentsFunctor C := by
  apply Localization.Construction.uniq
  rw [← Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac, Functor.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift_fac, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.zeroLevelComponentsFunctor_fac]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
