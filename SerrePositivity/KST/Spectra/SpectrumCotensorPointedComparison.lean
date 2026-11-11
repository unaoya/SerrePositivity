module

public import SerrePositivity.KST.Spectra.SpectrumCotensorMappingEquivalence
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorComposition
public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionNaturality

/-!
概要：BF cotensor の実際の比較を点つき射として公開し、全 Hom パラメータとの両立を示す。
方針：置換射影の後合成と厳密な cotensor 交換の豊穣自然性を合成する。
規約：選んだ cotensorPost の関手法則を仮定しない。
使われ方：普遍評価による coherent な cotensor の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の BF 置換射影で定まる点つき Hom 比較。 -/
def cotensorPointedMappingComparison (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    RawSpectrumMapping.pointedSpace X (cotensor A Y).toKanSequence ⟶
      (ihom A).obj (RawSpectrumMapping.pointedSpace X Y.toKanSequence) :=
  RawSpectrumMapping.pointedPost X (cotensorProjection A Y) ≫
    RawSpectrumMapping.cotensorComparison X Y.toKanSequence A

/-- 基点を忘れた比較は既存の同値の順写像そのもの。 -/
lemma cotensorPointedMappingComparison_right (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    (cotensorPointedMappingComparison X Y A).right =
      (cotensorMappingEquivalence X Y A).hom := rfl

/-- 比較は同値であるだけでなく、実際の自明 Kan fibration である。 -/
lemma cotensorPointedMappingComparison_trivialKanFibration (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cotensorPointedMappingComparison X Y A).right := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (RawSpectrumMapping.post X (cotensorProjection A Y) ≫
    (PointedSimplicialSet.forget.mapIso
      (RawSpectrumMapping.cotensorIso X Y.toKanSequence A)).hom)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (RawSpectrumMapping.cotensorProjection_rlp X Y A)
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- BF cotensor 比較は源の全 Hom パラメータでの合成と可換。 -/
lemma cotensorPointedMappingComparison_composition (X Y Z : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    RawSpectrumMapping.pointedComposition X Y (cotensor A Z).toKanSequence ≫
        cotensorPointedMappingComparison X Z A =
      (𝟙 (RawSpectrumMapping.pointedSpace X Y.toKanSequence) ⊗ₘ
        cotensorPointedMappingComparison Y Z A) ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map (RawSpectrumMapping.pointedSpace X Y.toKanSequence) A
        (RawSpectrumMapping.pointedSpace Y Z.toKanSequence) ≫
      (ihom A).map (RawSpectrumMapping.pointedComposition X Y Z.toKanSequence) := by
  dsimp only [cotensorPointedMappingComparison]
  rw [← Category.assoc, RawSpectrumMapping.pointedComposition_post, Category.assoc,
    RawSpectrumMapping.cotensorComparison_composition]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

end SerrePositivity.KST.Spectra.OmegaSpectrum
