module

public import SerrePositivity.KST.Spectra.SpectrumCotensorGradedEvaluation
public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleFunctors

/-!
概要：BF cotensor の評価の豊穣自然性を、基礎単体集合の全直積パラメータへ移す。
方針：smash 商の自然性・braiding との両立と元の Hom 合成の比較を使う。
規約：元の評価を保持する。使われ方：パラメータ付き円柱の coherent nerve。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance unpointedEvaluationSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の cotensor の評価は、基礎単体集合でも全パラメータで豊穣自然。 -/
def unpointedGradedEvaluation (A : PointedSimplicialSet.{u}) :
    GradedNatTrans (Center.ofBraidedObj A.right) (cotensorEnriched A) (sourceEnriched A) where
  app X := (cotensorEvaluation A X.val).right
  naturality X Y := by
    let P := pointedSpace A X.val Y.val
    have h := congrArg (fun f ↦ PointedSimplicialSet.productToSmash A P ≫ f.right)
      (((condition_iff A X.val Y.val _ _).mp (condition A X.val Y.val)).symm)
    simp only [Under.comp_right] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_braiding A P)] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_naturality
      (cotensorMap A X.val Y.val) (cotensorEvaluation A Y.val))] at h
    rw [← reassoc_of% (PointedSimplicialSet.productToSmash_naturality
      (cotensorEvaluation A X.val) (sourceMap A X.val Y.val))] at h
    rw [RawSpectrumMapping.productToSmash_pointedComposition,
      RawSpectrumMapping.productToSmash_pointedComposition] at h
    exact h

/-- 基点を忘れた豊穣自然変換の各対象での評価は元の普遍評価そのもの。 -/
lemma unpointedGradedEvaluation_app (A : PointedSimplicialSet.{u}) (X : Object A) :
    (unpointedGradedEvaluation A).app X = (cotensorEvaluation A X.val).right := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
