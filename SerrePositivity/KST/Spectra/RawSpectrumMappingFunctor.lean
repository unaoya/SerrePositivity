module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
概要：一般の Kan 列を標的とする元の整合写像空間を厳密な点つき関手にする。
方針：実際の後合成と、評価で証明した恒等・合成法則を用いる。
規約：BF 標的に限定しない。使われ方：小図式の homotopy end との自然な比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 整合写像空間は一般の Kan 列について厳密な点つき関手。 -/
def pointedFunctor (X : OmegaSpectrum.{u}) : KanSequence.{u} ⥤ PointedSimplicialSet.{u} where
  obj := pointedSpace X
  map := pointedPost X
  map_id Y := by
    apply Under.UnderMorphism.ext
    exact post_id X Y
  map_comp p q := by
    apply Under.UnderMorphism.ext
    exact post_comp X p q

/-- 各段の点つき評価を、全 Kan 列について自然変換へまとめる。 -/
def pointedEvaluationTransformation (X : OmegaSpectrum.{u}) (n : ℕ) :
    pointedFunctor X ⟶ KanSequence.levelEvaluation n ⋙
      PointedObject.basedHomFunctor (X.level n).space where
  app Y := pointedEvaluation X Y n
  naturality _ _ p := pointedPost_evaluation X p n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
