module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftExtension
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の図式を制限した関手の相対左 Kan 条件の標準局所余錐による表示。
方針：恒等変換の定値な局所輸送を選び、他の輸送との選択不変性を使う。
規約：包含に沿う関手の条件を、指定変換つきの既存の型に接続する。
使われ方：全部分圏から相対左 Kan 拡張されている関手の頂点条件。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：元の関手の制限から恒等変換で相対左 Kan 拡張されている点ごとの条件。
方針：各頂点の標準局所余錐に U 余極限性を課す。
規約：δ は任意の射。全部分圏の場合は包含を入力する。
使われ方：関手圏の相対制限の始点となる関手の標準条件。 -/
def IsRelativeLeftKanExtendedFrom {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) : Prop :=
  ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)

/-- 概要：恒等の指定変換の局所余錐の輸送は定値に選べる。
方針：標準局所余錐を時刻によらずそのまま使う。
規約：元の図式は δ による F の制限。
使われ方：標準局所条件と指定変換つきの相対左 Kan 条件の比較。 -/
def kanRelativeLeftReflTransport {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ (δ ≫ F) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)) c where
  family := snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val
  finish := by rfl
  diagram := by
    change snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val) =
        snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ (δ ≫ F) c
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).property]
  fixedVertex := by rfl

/-- 概要：標準局所余錐の相対左 Kan 条件は恒等変換つきの相対左 Kan 条件と同値。
方針：定値な局所輸送を選び、他の局所輸送の普遍性を同じ輸送へ移す。
規約：U は inner fibration、標的 D と E は quasicategory。
使われ方：原典の包含からの相対 Kan 条件を既存の指定変換の模型へ接続する。 -/
lemma kanIsRelativeLeftKanExtendedFrom_iff_refl_extension {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) (F : C ⟶ D) :
    IsRelativeLeftKanExtendedFrom U δ F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtension U δ (δ ≫ F) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (δ ≫ F)) := by
  have he (c : C _⦋0⦌) : (kanRelativeLeftReflTransport δ F c).cocone =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c := Subtype.ext rfl
  constructor
  · intro h c
    refine ⟨kanRelativeLeftReflTransport δ F c, ?_⟩
    rw [he]
    exact h c
  · intro h c
    obtain ⟨t, ht⟩ := h c
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransport_isRelativeColimit_iff U t
      (kanRelativeLeftReflTransport δ F c)).1 ht
    rw [he] at hs
    exact hs

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.2.13"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom
attribute [cite HTT "4.3.2.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom
