module

public import SerrePositivity.KST.Spectra.D3CommonCoherentComparison
public import SerrePositivity.KST.Spectra.AdjointLoopRelativeProjectionNaturality

/-!
概要：共通 Hom の比較射の自然性を、元の補助標的への同じ右射影まで回収する。
方針：同じ比較正方形に元の q_Y を後合成し、元の FullCompatible の右条件を使う。
規約：左包含の自然性だけから右射影を結論しない。
使われ方：d3b② の共通比較と元の補助単位の全 Hom 整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonProjectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 共通対象の全 Hom は元の補助標的への右脚も厳密に保つ。 -/
@[reassoc]
lemma common_right_projection (X Y : OmegaSpectrum.{u}) :
    commonRefinedMap X Y ≫ RawSpectrumMapping.post (commonRefinement X) (commonProjection Y) =
      commonBaseMap X Y ≫ fullOriginalMap X Y ≫
        (projectionParameterFamily X Y _ (universalParameterHom X Y)).right ≫
          RawSpectrumMapping.pre (commonComparison X) (target Y) := by
  have h := spectrumWhiskeredProjection (commonComparison X) (commonComparison Y)
    (projection Y) (commonRefinedMap X Y) (commonMiddleMap X Y) (common_right_whiskered X Y)
  change commonRefinedMap X Y ≫
    RawSpectrumMapping.post (commonRefinement X) (commonProjection Y) = _ at h
  rw [h]
  dsimp only [commonMiddleMap]
  rw [Category.assoc, ← Category.assoc (fullReplacedMap X Y), fullCompatible_right_condition]
  simp only [Category.assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
