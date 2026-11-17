module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentsLocalizationLift

/-!
# DK の連結成分の圏と普通の局所化の同値

概要：Dwyer–Kan の実際の Hom の π₀ と普通の局所化の Hom を同じ augmentation で比較する。
方針：構成的な lift の一意性と零次の全射の連結成分関手で両逆則を証明する。
規約：高次の Hom の弱同値や ∞ 局所化の普遍性とは区別する。
使われ方：既存 Map^h の π₀ 同定との元の射に関する正規化。
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

/-- 概要：零次の全射の比較は元の余単位の局所化像（Dwyer–Kan）。
方針：同じ標準対象表示と augmentation の移送を相殺する。
規約：形式逆を含む零次の全ての射を扱う。
使われ方：比較と持ち上げの反対側の逆則。 -/
lemma localizationZeroHom_augmentation {X Y : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y)) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).map f := by
  change eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object C (op ⦋0⦌) X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionAugmentation_object C (op ⦋0⦌) Y) = _
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：零次の全射の類は比較して持ち上げると元に戻る（Dwyer–Kan）。
方針：零次の局所化の関手等式を同じ射で評価する。
規約：元の射の零単体の類を保持する。
使われ方：全 π₀ の類への逆則の拡張。 -/
lemma localizationComponentsLift_augmentation_zero {X Y : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y)) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C).map
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C).map (SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f))) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f) := by
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C).map
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f)) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom_augmentation]
  have h := Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.strictLocalizationCounit_comp_componentsLift C) f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at h
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C).map
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).map f) =
      SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C f) at h
  exact h

/-- 概要：同じ augmentation の後の持ち上げは連結成分の圏で恒等（Dwyer–Kan）。
方針：全射の類を零単体に戻し、零次の標準対象表示で逆則を使う。
規約：元の Hom の π₀ 全体について証明する。
使われ方：普通の局所化との圏同値。 -/
lemma localizationComponentsAugmentation_comp_lift :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C =
      𝟭 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C).map ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C).map a) = a
  induction a using SSet.π₀.rec with
  | mk f =>
    let g := eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_zero C X).symm ≫ f ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizedFreeResolutionObject_zero C Y)
    have hg : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom C g = f := by
      simp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationZeroHom, g, Category.assoc]
    rw [← hg]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift_augmentation_zero C g

/-- 概要：実際の DK Hom の連結成分の圏は普通の局所化と同値（Dwyer–Kan）。
方針：元の augmentation と構成的な持ち上げの厳密な両逆則を使う。
規約：順関手は元の augmentation そのもの。
使われ方：既存の Map^h の π₀ 比較との照合。 -/
def localizationComponentsEquivalence : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationComponents C ≌ C.weakEquivalences.Localization
    where
  functor := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation C
  inverse := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift C
  unitIso := eqToIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation_comp_lift C).symm
  counitIso := eqToIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift_comp_augmentation C)
  functor_unitIso_comp X := by simp

/-- 概要：元の生成関手は普通の圏として指定弱同値の局所化（Dwyer–Kan）。
方針：構成済みの普通の局所化へ同じ比較同値の逆を後合成する。
規約：普通の局所化の普遍性。∞ 圏での普遍性は後続。
使われ方：π₀ 比較の普遍性と元の指定弱同値の照合。 -/
lemma localizationComponentsQ_isLocalization :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C).IsLocalization C.weakEquivalences :=
  Functor.IsLocalization.of_equivalence_target C.weakEquivalences.Q C.weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsQ C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsEquivalence C).symm
    (eqToIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsLift_fac C))

/-- 概要：元の DK Hom の π₀ は同じ普通の局所化 Hom と同値（Dwyer–Kan）。
方針：同じ比較圏の同値の充満忠実性で Hom の同値を取り出す。
規約：順写像は元の augmentation の π₀ 比較そのもの。
使われ方：元の Map^h の零次の同定との比較。 -/
def localizationHomPiZeroEquiv (X Y : C.category) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y) ≃
      (C.weakEquivalences.Q.obj X ⟶ C.weakEquivalences.Q.obj Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsEquivalence C).fullyFaithfulFunctor.homEquiv

/-- 概要：π₀ 同値は元の生成射の類を同じ Q の像へ送る（Dwyer–Kan）。
方針：同じ augmentation の元の一文字の射の正規化を使う。
規約：元の局所化射を保持する。
使われ方：DK/Map^h の比較の元の射での照合。 -/
lemma localizationHomPiZeroEquiv_arrow {X Y : C.category} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroEquiv C X Y (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowClass C f) =
      C.weakEquivalences.Q.map f :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComponentsAugmentation_arrow C f

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
