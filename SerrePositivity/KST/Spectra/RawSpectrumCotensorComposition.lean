module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedComposition
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrengthNaturality

/-!
概要：元の cotensor 交換の、源の全 Hom パラメータに関する豊穣自然性。
方針：各段の評価で、内部 Hom の合成・交換の両立と strength の自然性を使う。
規約：smash パラメータ上の実際の点つき射の等式。通常の源射への自然性より強い。
使われ方：Hom–end 比較の豊穣自然性と coherent な極限錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance cotensorCompositionSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- cotensor の厳密な交換は、源の全 Hom パラメータによる合成と可換。 -/
lemma cotensorComparison_composition (X Y : OmegaSpectrum.{u})
    (Z : KanSequence.{u}) (A : PointedSimplicialSet.{u}) :
    pointedComposition X Y (KanSequence.mapping A Z) ≫ cotensorComparison X Z A =
      (𝟙 (pointedSpace X Y.toKanSequence) ⊗ₘ cotensorComparison Y Z A) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map (pointedSpace X Y.toKanSequence) A (pointedSpace Y Z) ≫
          (ihom A).map (pointedComposition X Y Z) := by
  apply ihom_pointed_hom_ext X Z A
  intro n
  conv_lhs =>
    rw [Category.assoc, cotensorComparison_evaluation]
    dsimp only [exchangeFamily]
    rw [← Category.assoc, pointedComposition_evaluation]
  conv_rhs =>
    rw [Category.assoc, Category.assoc, ← Functor.map_comp,
      pointedComposition_evaluation]
  dsimp only [pointedCompositionFamily]
  change ((pointedEvaluation X Y.toKanSequence n ⊗ₘ
      pointedEvaluation Y (KanSequence.mapping A Z) n) ≫
      comp (X.level n).space (Y.level n).space ((ihom A).obj (Z.level n).space)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Z.level n).space).hom = _
  conv_rhs =>
    rw [Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.natural_assoc,
      ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
      cotensorComparison_evaluation]
    dsimp only [exchangeFamily]
    rw [← tensorHom_comp_whiskerLeft, Category.assoc]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.composition]
  simp only [id_tensorHom]
  rfl


end SerrePositivity.KST.Spectra.RawSpectrumMapping
