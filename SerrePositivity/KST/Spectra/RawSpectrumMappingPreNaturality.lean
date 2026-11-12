module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition
public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor

/-!
概要：元の点つき整合写像空間の前合成と、標的列の後合成の厳密な可換性。
方針：全ての段で閉構造の pre の自然性を適用する。
規約：射は元の豊穣合成から構成済み。使われ方：源を動かす Hom-end 比較の自然変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 源の前合成と一般の Kan 列の後合成は、全単体上で厳密に可換。 -/
lemma pointedPre_post {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    {Z T : KanSequence.{u}} (p : Z ⟶ T) :
    pointedPost Y p ≫ pointedPre f T = pointedPre f Z ≫ pointedPost X p := by
  apply pointed_hom_ext X T
  intro n
  conv_lhs =>
    rw [Category.assoc, pointedPre_evaluation, ← Category.assoc,
      pointedPost_evaluation, Category.assoc]
  conv_rhs =>
    rw [Category.assoc, pointedPost_evaluation, ← Category.assoc,
      pointedPre_evaluation, Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact congrArg (pointedEvaluation Y Z n ≫ ·)
    ((MonoidalClosed.pre (f.app n)).naturality (p.app n))

/-- 源の元の BF 射を動かした点つき Hom の厳密な自然変換。 -/
def pointedPreTransformation {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    pointedFunctor Y ⟶ pointedFunctor X where
  app := pointedPre f
  naturality _ _ p := pointedPre_post f p

end SerrePositivity.KST.Spectra.RawSpectrumMapping
