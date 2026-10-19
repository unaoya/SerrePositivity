module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluation
public import SerrePositivity.KST.Spectra.PointedExchangeVertices
public import SerrePositivity.KST.Spectra.RawSpectrumPointedCompositionComparison
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence

/-!
概要：元の cotensor 普遍評価への前合成を、元の BF Hom の直積合成で計算する。
方針：点つき uncurry の smash 商、交換と商の自然性、元の合成との一致を使う。
規約：任意の点つきパラメーターに成立。使われ方：BK 切断点の全 Hom 比較族の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 基点を忘れた普遍評価の前合成は、元の BF Hom の直積パラメーターの合成そのもの。 -/
lemma cotensorEvaluationPrecomposition_underlying (X Y : OmegaSpectrum.{u})
    (A : PointedSimplicialSet.{u}) :
    uncurry ((cotensorEvaluationPrecomposition X Y A).right ≫
      PointedObject.basedHomι A (RawSpectrumMapping.pointedSpace X Y.toKanSequence)) =
      (β_ A.right (mappingSpace X (cotensor A Y))).hom ≫
        mappingSpace X (cotensor A Y) ◁ (cotensorEvaluation A Y).right ≫
          mappingComposition X (cotensor A Y) Y := by
  rw [← PointedMapping.uncurry_quotient, cotensorEvaluationPrecomposition, uncurry_curry]
  simp only [Under.comp_right]
  let M := RawSpectrumMapping.pointedSpace X (cotensor A Y).toKanSequence
  change PointedSimplicialSet.productToSmash A M ≫ (β_ A M).hom.right ≫
      (M ◁ cotensorEvaluation A Y).right ≫
        (RawSpectrumMapping.pointedComposition X (cotensor A Y) Y.toKanSequence).right = _
  rw [← reassoc_of% (PointedSimplicialSet.productToSmash_braiding A M)]
  have hn := PointedSimplicialSet.productToSmash_naturality (𝟙 M) (cotensorEvaluation A Y)
  simp only [Under.id_right, id_tensorHom] at hn
  change M.right ◁ (cotensorEvaluation A Y).right ≫ PointedSimplicialSet.productToSmash M _ =
    PointedSimplicialSet.productToSmash M A ≫ (M ◁ cotensorEvaluation A Y).right at hn
  rw [← reassoc_of% hn, RawSpectrumMapping.productToSmash_pointedComposition]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
