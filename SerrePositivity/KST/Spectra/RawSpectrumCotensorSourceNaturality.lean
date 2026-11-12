module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPreNaturality
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality

/-!
概要：元の cotensor 交換は、BF 源の射による前合成と厳密に可換。
方針：全段評価と閉構造の源交換の第一変数の自然性を使う。
規約：全整合族の点つき射の等式。使われ方：Hom-end 交換の源変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の源の BF 射による前合成は、全整合族の cotensor 交換と可換。 -/
lemma cotensorComparison_pre_source {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (Z : KanSequence.{u}) (A : PointedSimplicialSet.{u}) :
    pointedPre f (KanSequence.mapping A Z) ≫ cotensorComparison X Z A =
      cotensorComparison Y Z A ≫ (ihom A).map (pointedPre f Z) := by
  apply ihom_pointed_hom_ext X Z A
  intro n
  rw [Category.assoc, cotensorComparison_evaluation]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, pointedPre_evaluation,
    CategoryTheory.Functor.map_comp, ← Category.assoc, cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, pointedPre_evaluation, Category.assoc]
  change pointedEvaluation Y (KanSequence.mapping A Z) n ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (f.app n) ((ihom A).obj (Z.level n).space) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Z.level n).space).hom) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left (f.app n) A (Z.level n).space
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
  exact congrArg (pointedEvaluation Y (KanSequence.mapping A Z) n ≫ ·) h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
