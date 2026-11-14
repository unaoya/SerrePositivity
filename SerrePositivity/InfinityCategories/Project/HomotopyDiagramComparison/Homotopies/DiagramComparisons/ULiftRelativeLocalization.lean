module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.StrictLocalization
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.HomCongr

/-!
# Hom の宇宙を上げた相対圏の普通の局所化

概要：Dwyer–Kan 入力の Hom の ULift と元の普通の局所化の同値を構成する。
方針：同じ up・down を構成的に局所化し、厳密な因子化と一意性を使う。
規約：元の対象・射・指定弱同値を保持し、モデル構造を要求しない。
使われ方：E 代数の DK Hom と既存の Map^h の π₀ の同じ比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization

open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- 概要：元の指定弱同値を Hom の ULift へ移す（Dwyer–Kan）。
方針：同じ down による逆像を取る。
規約：元の指定弱同値を変更しない。
使われ方：DK 入力の Hom 宇宙の調整。 -/
abbrev liftedWeakEquivalences : MorphismProperty (ULiftHom.{w} C) :=
  W.inverseImage (ULiftHom.down.{v, u, w} (C := C))

/-- 概要：Hom の ULift から元の相対圏への同じ down（Dwyer–Kan）。
方針：指定弱同値の逆像の定義を使う。
規約：対象と元の射を保持する。
使われ方：普通の局所化の比較の順関手。 -/
def down : LocalizerMorphism (liftedWeakEquivalences.{u, v, w} W) W :=
  ⟨ULiftHom.down.{v, u, w}, fun _ _ _ hf => hf⟩

/-- 概要：元の相対圏から Hom の ULift への同じ up（Dwyer–Kan）。
方針：up の直後の down は元の射であることを使う。
規約：元の指定弱同値を保持する。
使われ方：普通の局所化の比較の逆関手。 -/
def up : LocalizerMorphism W (liftedWeakEquivalences.{u, v, w} W) :=
  ⟨ULiftHom.up.{v, u, w}, fun _ _ _ hf => hf⟩

/-- 概要：局所化した down の後の up は恒等（Dwyer–Kan）。
方針：構成的局所化の一意性と同じ順逆の厳密な因子化を使う。
規約：元の ULift の局所化上の関手等式。
使われ方：同値の単位。 -/
lemma down_up : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (down.{u, v, w} W) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (up W) =
    𝟭 (liftedWeakEquivalences.{u, v, w} W).Localization := by
  apply Localization.Construction.uniq
  rw [← Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac, Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac]
  rfl

/-- 概要：局所化した up の後の down は恒等（Dwyer–Kan）。
方針：構成的局所化の一意性と同じ順逆の厳密な因子化を使う。
規約：元の圏の局所化上の関手等式。
使われ方：同値の余単位。 -/
lemma up_down : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (up.{u, v, w} W) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (down W) =
    𝟭 W.Localization := by
  apply Localization.Construction.uniq
  rw [← Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac, Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac]
  rfl

/-- 概要：Hom の ULift は元の普通の局所化を変えない（Dwyer–Kan）。
方針：同じ down と up の局所化の厳密な両逆を束ねる。
規約：順関手は元の down の構成的な局所化。
使われ方：DK 相対圏と元の E 代数の局所化の同じ比較。 -/
def equivalence : (liftedWeakEquivalences.{u, v, w} W).Localization ≌ W.Localization where
  functor := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (down W)
  inverse := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (up W)
  unitIso := eqToIso (down_up W).symm
  counitIso := eqToIso (up_down W)
  functor_unitIso_comp X := by simp

/-- 概要：元の対象の局所化 Hom を同じ down で比較する（Dwyer–Kan）。
方針：同じ同値の Hom 作用を元の厳密な因子化の対象同型で移す。
規約：両対象は元の局所化像を保持する。
使われ方：π₀ 比較の Hom 宇宙の調整。 -/
def homEquiv (X Y : ULiftHom.{w} C) :
    ((liftedWeakEquivalences W).Q.obj X ⟶ (liftedWeakEquivalences W).Q.obj Y) ≃
      (W.Q.obj X.objDown ⟶ W.Q.obj Y.objDown) :=
  (equivalence W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (eqToIso (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (down W)) X))
      (eqToIso (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (down W)) Y)))

/-- 概要：同じ Hom 同値は元の射の局所化像を保つ（Dwyer–Kan）。
方針：厳密な因子化を Hom に評価し、対象の移送を相殺する。
規約：元の Q と同じ down による射。
使われ方：元の E 代数射での比較の正規化。 -/
lemma homEquiv_map {X Y : ULiftHom.{w} C} (f : X ⟶ Y) :
    homEquiv W X Y ((liftedWeakEquivalences W).Q.map f) =
      W.Q.map ((ULiftHom.down.{v, u, w} (C := C)).map f) := by
  have h := Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (down.{u, v, w} W)) f
  change eqToHom (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (down W)) X).symm ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (down W)).map ((liftedWeakEquivalences W).Q.map f) ≫
      eqToHom (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (down W)) Y) = _
  simp only [Functor.comp_map] at h
  rw [h]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization
