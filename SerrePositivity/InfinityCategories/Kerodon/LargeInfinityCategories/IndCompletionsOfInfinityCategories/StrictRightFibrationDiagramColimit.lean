module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.StrictKappaFilteredColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationInfinity
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
概要：固定底上の通常の filtered right fibration 図式の実際の余極限対象。
方針：全空間の余極限に同じ底への射を降ろし、既証の持ち上げ性の保存を適用する。
規約：元の余錐の脚と射影を保持する。coherent な余極限性はまだ主張しない。
使われ方：Indκ の元の圏の strict な閉性と、前層余極限との比較への入力。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 同じ固定底上の図式の全空間の通常の図式。 -/
def rightFibrationTotalDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) : I ⥤ SSet.{u} where
  obj i := (F.obj i).val.left
  map f := (F.map f).left

/-- 各段の元の射影がなす、同じ底への余錐。 -/
def rightFibrationProjectionCocone (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    Cocone (rightFibrationTotalDiagram F) where
  pt := B
  ι := { app i := (F.obj i).val.hom, naturality _ _ f := by
           exact (Over.w (F.map f)).trans (Category.comp_id _).symm }

/-- 元の全空間の余極限から同じ底への射影。 -/
def strictRightFibrationColimitProjection (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    colimit (rightFibrationTotalDiagram F) ⟶ B :=
  colimit.desc _ (rightFibrationProjectionCocone F)

@[reassoc (attr := simp)]
lemma strictRightFibrationColimitProjection_ι (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (i : I) :
    colimit.ι (rightFibrationTotalDiagram F) i ≫ strictRightFibrationColimitProjection F =
      (F.obj i).val.hom := colimit.ι_desc _ _

/-- 通常の filtered 余極限の同じ射影は right fibration。 -/
instance strictRightFibrationColimitProjection_rightFibration [IsFiltered I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (strictRightFibrationColimitProjection F) := by
  have : IsConnected I := IsFiltered.isConnected I
  let η : rightFibrationTotalDiagram F ⟶ (Functor.const I).obj B :=
    (rightFibrationProjectionCocone F).ι
  have (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (η.app i) := (F.obj i).property
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibration_of_filtered_isColimit η (colimit.isColimit _)
    (isColimitConstCocone I B) _ (fun i => by
      exact (strictRightFibrationColimitProjection_ι F i).trans (Category.comp_id _).symm)

/-- 同じ底上の right fibration として束ねた通常の余極限対象。 -/
def strictRightFibrationColimit [IsFiltered I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B := ⟨Over.mk (strictRightFibrationColimitProjection F),
      strictRightFibrationColimitProjection_rightFibration F⟩

/-- 元の底が quasicategory なら、各 right fibration の全空間も quasicategory。 -/
instance rightFibrationObject_total_quasicategory [Quasicategory B]
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) : Quasicategory p.val.left :=
  quasicategory_of_innerFibration p.val.hom

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] [IsCardinalFiltered I κ]

/-- 同じ元の圏の通常の余極限は κ-filtered。 -/
lemma strictRightFibrationColimit_isKappaFiltered
    [Quasicategory B] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left] :
    letI : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (strictRightFibrationColimit F).val.left := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  have (i : I) : Quasicategory ((rightFibrationTotalDiagram F).obj i) :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  have : Quasicategory (colimit.cocone (rightFibrationTotalDiagram F)).pt :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.quasicategory_of_filtered_isColimit (colimit.isColimit _)
  have (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ ((rightFibrationTotalDiagram F).obj i) :=
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i).val.left)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_strict_isColimit (colimit.isColimit _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
