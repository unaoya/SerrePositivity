module

public import SerrePositivity.KST.Spectra.FreeActionEndKan

/-!
概要：自由作用の end と通常の内部 Hom の比較の係数への自然性。
方針：第一座標 1 への制限の後合成の公式を Yoneda の比較へ移す。
規約：係数の射は厳密な同変射。
使われ方：Goerss–Jardine VIII §2。cochain の各次数の π_* 同型保存への入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：係数の同変射が誘導する作用図式の自然変換。
方針：作用と一対象圏の図式との同値を使う。
規約：小さい一対象圏への持ち上げを含む。
使われ方：Goerss–Jardine VIII §2。自由作用の end の係数比較。 -/
def coefficientsMap {G : Type u} [Group G] {B C : Action SSet.{u} G} (τ : B ⟶ C) :
    coefficients B ⟶ coefficients C :=
  Functor.whiskerLeft AsSmall.down (Action.FunctorCategoryEquivalence.functor.map τ)

lemma restrict_post {G : Type u} [Group G] (S : Type u) {B C : Action SSet.{u} G}
    {A : SSet.{u}}
    (s : weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B)
    (τ : B ⟶ C) :
    restrict S C (s ≫ coefficientsMap τ) = restrict S B s ≫ τ.hom := by
  ext n x
  rfl

lemma sectionsUncurry_post {I : Type u} [SmallCategory I] {W H H' : I ⥤ SSet.{u}}
    {A : SSet.{u}} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) (τ : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W τ) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f ≫ τ := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H' A).symm.injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W τ)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f ≫ τ)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_uncurry]

/-- 概要：自由作用の end の Hom の同値は係数の同変射に自然。
方針：制限の後合成の公式と curry の後合成の公式を使う。
規約：パラメーターの Kan 性は不要。
使われ方：Goerss–Jardine VIII §2。内部 Hom との比較の係数の自然性。 -/
lemma homEquiv_post {G : Type u} [Group G] (S : Type u) {B C : Action SSet.{u} G}
    {A : SSet.{u}} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) (τ : B ⟶ C) :
    homEquiv S C A (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (weight S) (coefficientsMap τ)) =
      homEquiv S B A f ≫ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).map τ.hom := by
  rw [homEquiv_apply, homEquiv_apply, sectionsUncurry_post, restrict_post, curry_natural_right]

lemma endIso_hom {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G) :
    (endIso S B).hom = homEquiv S B (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) (𝟙 _) := rfl

/-- 概要：自由作用の end と内部 Hom の同型は係数の同変射に自然。
方針：Hom の同値の両変数の自然性を恒等射へ適用する。
規約：実際の比較同型の射についての厳密な等式。
使われ方：Goerss–Jardine VIII §2。群作用の cochain の各段のホモトピー比較。 -/
lemma endIso_natural {G : Type u} [Group G] (S : Type u)
    {B C : Action SSet.{u} G} (τ : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (weight S) (coefficientsMap τ) ≫ (endIso S C).hom =
      (endIso S B).hom ≫ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).map τ.hom := by
  have hl := homEquiv_pre S C (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (weight S) (coefficientsMap τ)) (𝟙 _)
  rw [Category.comp_id] at hl
  have hr := homEquiv_post S (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B))) τ
  rw [Category.id_comp] at hr
  rw [endIso_hom, endIso_hom]
  exact hl.symm.trans hr

end

end SerrePositivity.KST.Spectra.FreeActionFamily
