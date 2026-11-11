module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso
public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor
public import SerrePositivity.KST.Spectra.KanSequenceMappingFunctor
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：整合写像空間と内部 Hom の交換を、Kan 列の標的について自然同型へまとめる。
方針：全ての段の評価へ戻し、二重内部 Hom の交換の自然性を使う。
規約：整合族全体の点つき射の等式。使われ方：homotopy end の図式の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 内部 Hom 交換の順射は、標的 Kan 列の任意の厳密な射について自然。 -/
lemma cotensorComparison_natural (X : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u})
    {Y Z : KanSequence.{u}} (p : Y ⟶ Z) :
    pointedPost X (KanSequence.mappingPost A p) ≫ cotensorComparison X Z A =
      cotensorComparison X Y A ≫ (ihom A).map (pointedPost X p) := by
  apply ihom_pointed_hom_ext X Z A
  intro n
  rw [Category.assoc, cotensorComparison_evaluation]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, pointedPost_evaluation,
    CategoryTheory.Functor.map_comp, ← Category.assoc, cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, pointedPost_evaluation, Category.assoc]
  exact congrArg (pointedEvaluation X (KanSequence.mapping A Y) n ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post (X.level n).space A (p.app n))

/-- 任意の固定した点つき源に対する、全 Kan 列上の実際の自然な cotensor 交換同型。 -/
def cotensorNatIso (X : OmegaSpectrum.{u}) (A : PointedSimplicialSet.{u}) :
    KanSequence.mappingFunctor A ⋙ pointedFunctor X ≅ pointedFunctor X ⋙ ihom A :=
  NatIso.ofComponents (fun Y ↦ cotensorIso X Y A)
    (fun p ↦ cotensorComparison_natural X A p)

/-- 内部 Hom の源の制限も、整合写像空間全体の交換と厳密に可換。 -/
lemma cotensorComparison_pre (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) :
    pointedPost X (KanSequence.mappingPre i Y) ≫ cotensorComparison X Y A =
      cotensorComparison X Y B ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (pointedSpace X Y) := by
  apply ihom_pointed_hom_ext X Y A
  intro n
  rw [Category.assoc, cotensorComparison_evaluation]
  have hn := (MonoidalClosed.pre i).naturality (pointedEvaluation X Y n)
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc, ← hn,
    ← Category.assoc, cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, pointedPost_evaluation, Category.assoc]
  change pointedEvaluation X (KanSequence.mapping B Y) n ≫
      (PointedObject.basedHomMap (X.level n).space
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact congrArg (pointedEvaluation X (KanSequence.mapping B Y) n ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right (X.level n).space i (Y.level n).space)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
