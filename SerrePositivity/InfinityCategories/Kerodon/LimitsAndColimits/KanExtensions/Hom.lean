module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomotopyInvariant
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomotopyInvariant
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右 Kan 拡張条件を h Fun の指定した射そのものに対して述べる。
方針：A1c の代表ホモトピーを使い、h 不変性により任意の代表との一致を証明する。
規約：代表は条件の一部として追加せず、任意の代表を使って判定できる。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG）、随伴・大域的な Kan 拡張の普遍性への入口。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：h Fun の射が右 Kan 拡張を与える条件。
方針：A1c の代表ホモトピーに点ごとの定義を適用する。
規約：任意の代表との一致は iff_of_representative で保証する。
使われ方：h Fun 内の自然変換による Kan 拡張の主張。 -/
def IsRightKanExtensionHom {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy α)

/-- 概要：h Fun の射が左 Kan 拡張を与える条件。
方針：A1c の代表ホモトピーに点ごとの定義を適用する。
規約：任意の代表との一致は iff_of_representative で保証する。
使われ方：h Fun 内の自然変換による Kan 拡張の主張。 -/
@[kerodon 02YG]
def IsLeftKanExtensionHom {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F)) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy β)

/-- 概要：右 Kan 条件は h Fun の射の任意の代表ホモトピーで判定できる。
方針：A1c の選んだ代表の類が元の射に一致することと h 不変性を使う。
規約：H は指定した α を表す。
使われ方：具体的な比較錐と h Fun の普遍性との往復。 -/
lemma isRightKanExtensionHom_iff_of_representative {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (δ ≫ F) F₀)
    (H : SSet.Homotopy (δ ≫ F) F₀)
    (hH : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = α) :
    IsRightKanExtensionHom δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtension_iff_of_homMk_eq δ F₀ F _ H ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α).trans hH.symm)

/-- 概要：左 Kan 条件は h Fun の射の任意の代表ホモトピーで判定できる。
方針：A1c の代表の類の仕様と h 不変性を使う。
規約：H は指定した β を表す。
使われ方：具体的な比較余錐と h Fun の普遍性との往復。 -/
lemma isLeftKanExtensionHom_iff_of_representative {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F₀ (δ ≫ F))
    (H : SSet.Homotopy F₀ (δ ≫ F))
    (hH : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = β) :
    IsLeftKanExtensionHom δ F₀ F β ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_iff_of_homMk_eq δ F₀ F _ H ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom β).trans hH.symm)

/-- 概要：実際のホモトピーを h Fun の射にしても右 Kan 条件は変わらない。
方針：そのホモトピー自身を代表として使う。
規約：標的 D の quasicategory 性のみを要求する。
使われ方：点ごとの定義から h Fun の定義への接続。 -/
lemma isRightKanExtensionHom_homotopy {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (H : SSet.Homotopy (δ ≫ F) F₀) :
    IsRightKanExtensionHom δ F₀ F
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F H :=
  isRightKanExtensionHom_iff_of_representative δ F₀ F _ H rfl

/-- 概要：実際のホモトピーを h Fun の射にしても左 Kan 条件は変わらない。
方針：そのホモトピー自身を代表として使う。
規約：標的 D の quasicategory 性のみを要求する。
使われ方：点ごとの定義から h Fun の定義への接続。 -/
lemma isLeftKanExtensionHom_homotopy {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (H : SSet.Homotopy F₀ (δ ≫ F)) :
    IsLeftKanExtensionHom δ F₀ F
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F H :=
  isLeftKanExtensionHom_iff_of_representative δ F₀ F _ H rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
