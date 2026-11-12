module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.IntervalMaximum
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定ホモトピーの矢印の時間を最大値で縮める正方形。
方針：二つの時間を最大値へ送り、元のホモトピーを評価する。
規約：パラメータ、最初の時間、矢印の時間の順。
使われ方：comma の矢印から標的の恒等矢印への変形の入力。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：パラメータを固定し二つの時間を最大値へ畳む。
方針：直積の結合子の後に区間の最大値を作用させる。
規約：始域の直積は左結合。
使われ方：comma 内の変形の正方形。 -/
def kanHomotopyMaximumAction (A : SSet.{u}) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ A ⊗ Δ[1] :=
  (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom ≫ (A ◁ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum)

/-- 概要：最初の時間を零に制限すると矢印の時間を保つ。
方針：結合子の端点と最大値の零端点。
規約：二番目の時間は変えない。
使われ方：変形の始点。 -/
lemma kanHomotopyMaximumAction_first_zero (A : SSet.{u}) :
    ((SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      kanHomotopyMaximumAction A = 𝟙 _ := by
  have hc : ((SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom =
        A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) := rfl
  rw [kanHomotopyMaximumAction, ← Category.assoc, hc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_zero, whiskerLeft_id]

/-- 概要：最初の時間を一に制限すると矢印の時間も一に固定する。
方針：最大値の一端点。
規約：パラメータは保つ。
使われ方：変形の終点。 -/
lemma kanHomotopyMaximumAction_first_one (A : SSet.{u}) :
    ((SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      kanHomotopyMaximumAction A = fst A Δ[1] ≫ SSet.ι₁ := by
  have hc : ((SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom =
        A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) := rfl
  rw [kanHomotopyMaximumAction, ← Category.assoc, hc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_one]
  rfl

/-- 概要：矢印の時間を零に制限すると最初の時間を保つ。
方針：結合子の端点と最大値の零端点。
規約：最初の時間は変えない。
使われ方：変形中の矢印の始域。 -/
lemma kanHomotopyMaximumAction_second_zero (A : SSet.{u}) :
    (SSet.ι₀ : A ⊗ (Δ[1] : SSet.{u}) ⟶ (A ⊗ Δ[1]) ⊗ Δ[1]) ≫
      kanHomotopyMaximumAction A = 𝟙 _ := by
  have hc : (SSet.ι₀ : A ⊗ (Δ[1] : SSet.{u}) ⟶ (A ⊗ Δ[1]) ⊗ Δ[1]) ≫
      (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom =
        A ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := rfl
  rw [kanHomotopyMaximumAction, ← Category.assoc, hc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_second_zero, whiskerLeft_id]

/-- 概要：矢印の時間を一に制限すると標的に定値になる。
方針：最大値の一端点。
規約：パラメータは保つ。
使われ方：変形中の矢印の標的。 -/
lemma kanHomotopyMaximumAction_second_one (A : SSet.{u}) :
    (SSet.ι₁ : A ⊗ (Δ[1] : SSet.{u}) ⟶ (A ⊗ Δ[1]) ⊗ Δ[1]) ≫
      kanHomotopyMaximumAction A = fst A Δ[1] ≫ SSet.ι₁ := by
  have hc : (SSet.ι₁ : A ⊗ (Δ[1] : SSet.{u}) ⟶ (A ⊗ Δ[1]) ⊗ Δ[1]) ≫
      (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom =
        A ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := rfl
  rw [kanHomotopyMaximumAction, ← Category.assoc, hc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_second_one]
  rfl

/-- 概要：元の矢印の時間から標的に固定した矢印へのホモトピー。
方針：最大値の正方形の第二因子を矢印の時間とする。
規約：始域は元の円柱全体。
使われ方：comma の持ち上げに使う変形中の矢印。 -/
def kanHomotopyMaximum {A X : SSet.{u}} {f g : A ⟶ X} (H : SSet.Homotopy f g) :
    SSet.Homotopy H.h (fst A (Δ[1] : SSet.{u}) ≫ g) where
  h := kanHomotopyMaximumAction A ≫ H.h
  h₀ := by rw [← Category.assoc, kanHomotopyMaximumAction_second_zero, Category.id_comp]; rfl
  h₁ := by rw [← Category.assoc, kanHomotopyMaximumAction_second_one, Category.assoc, H.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：変形の最初の時間零で元の矢印の族を回収する。
方針：最大値の正方形の零境界を使う。
規約：矢印の時間は保つ。
使われ方：comma の変形の始点の計算。 -/
lemma kanHomotopyMaximum_first_zero_h {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    ((SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (kanHomotopyMaximum H).h = H.h := by
  rw [kanHomotopyMaximum, ← Category.assoc, kanHomotopyMaximumAction_first_zero,
    Category.id_comp]

/-- 概要：変形の最初の時間一で標的の定値矢印を回収する。
方針：最大値の正方形の一境界と元のホモトピーの終点。
規約：パラメータは保つ。
使われ方：comma の変形の終点の計算。 -/
lemma kanHomotopyMaximum_first_one_h {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    ((SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      (kanHomotopyMaximum H).h = fst A Δ[1] ≫ g := by
  rw [kanHomotopyMaximum, ← Category.assoc, kanHomotopyMaximumAction_first_one,
    Category.assoc, H.h₁]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
