module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleFunctors
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedWhiskeredSquareComposition

/-!
概要：左右因子を保つ全 Hom の組上の元の相対 BF 左因子の厳密自然性。
方針：実引き戻しの左境界を豊穣単位パラメータの正方形へ移す。
規約：右射影の条件を保つ同じ写像空間を使う。
使われ方：元の包含を成分とする全図式同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance adjointLoopRelativeFullGradedInclusionLocal1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 概要：指定した相対左因子は全 Hom 上で厳密に豊穣自然。
方針：元の左境界を単位パラメータの豊穣正方形へ変換する。
規約：指定左因子と右射影を保つ同じ組を使う。
使われ方：全図式比較の成分の回収。 -/
def fullGradedInclusion :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      fullOriginalEnriched fullReplacedEnriched where
  app X := eHomEquiv SSet (inclusion X.val)
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    (inclusion X.val) (inclusion Y.val)
    (fullReplacedMap X.val Y.val) (fullOriginalMap X.val Y.val)).mp
      (full_left_whiskered X.val Y.val)).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
