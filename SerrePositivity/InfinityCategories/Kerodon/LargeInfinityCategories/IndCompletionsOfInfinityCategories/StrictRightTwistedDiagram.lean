module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeEdgewiseRightFibration

/-!
概要：元の right fibration 図式の twisted arrow と相対右端比較を全添字で自然に組む。
方針：元の底上の作用を引き戻しに写し、twisted arrow の両射影で自然性を検査。
規約：個別の切断は選ばない。使われ方：大域密度の指定変換を同じ全族で構成する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 元の全空間の終点を保つ、底の twisted arrow の引き戻しの通常図式。 -/
def strictRightTwistedElementsDiagram : I ⥤ SSet.{u} where
  obj i := pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) (F.obj i).val.hom
  map {i j} f := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (F.map f).left) (by
      rw [Category.assoc, Over.w]
      exact pullback.condition)
  map_id i := by
    apply pullback.hom_ext <;> simp
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  map_comp f g := by
    apply pullback.hom_ext <;> simp [Category.assoc]
    exact (Category.assoc _ _ _).symm

/-- 元の全空間の twisted arrow を、同じ通常の添字で動かす図式。 -/
def strictRightTwistedTotalDiagram : I ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor

/-- 相対右端比較は、元の図式の全ての作用に厳密に自然。 -/
def strictRightTwistedComparison :
    strictRightTwistedTotalDiagram F ⟶ strictRightTwistedElementsDiagram F where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison (F.obj i).val.hom
  naturality i j f := by
    apply pullback.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_fst,
        strictRightTwistedElementsDiagram, pullback.lift_fst]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (F.map f).left ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (F.obj j).val.hom =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map (F.obj i).val.hom
      rw [← Functor.map_comp, Over.w]
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_snd,
        strictRightTwistedElementsDiagram, pullback.lift_snd]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.map f).left ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison (F.obj i).val.hom ≫
          (pullback.snd _ _ ≫ (F.map f).left)
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality]

/-- 同じ自然比較の全成分は、元の right fibration の自明 Kan 比較。 -/
instance strictRightTwistedComparison_trivialKanFibration (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((strictRightTwistedComparison F).app i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_trivialKanFibration (F.obj i).val.hom

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
