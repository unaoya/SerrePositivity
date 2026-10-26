module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleEnrichment

/-!
概要：指定左右因子を保つ全 Hom の組から元の BF 対象と置換対象への豊穣射影。
方針：実引き戻しの二射影の厳密な単位・合成保存を使う。
規約：選択した持ち上げの通常関手性を仮定しない。
使われ方：補助単位と右射影を同時に保つ全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance adjointLoopRelativeFullCompatibleFunctorsLocal1 : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 概要：左右境界を保つ組のOriginal射影は全 Hom の実豊穣関手。
方針：二射影の厳密な単位・合成保存を使う。
規約：全単体上の元の射影を用いる。
使われ方：相対 BF の全図式比較。 -/
def fullOriginalEnriched :
    EnrichedFunctor SSet.{u} FullObject OmegaSpectrum.{u} where
  obj X := X.val
  map X Y := fullOriginalMap X.val Y.val
  map_id X := fullCompatibleIdentity_originalMap X.val
  map_comp X Y Z := fullCompatibleComposition_originalMap X.val Y.val Z.val

/-- 概要：左右境界を保つ組のReplaced射影は全 Hom の実豊穣関手。
方針：二射影の厳密な単位・合成保存を使う。
規約：全単体上の元の射影を用いる。
使われ方：相対 BF の全図式比較。 -/
def fullReplacedEnriched :
    EnrichedFunctor SSet.{u} FullObject OmegaSpectrum.{u} where
  obj X := middle X.val
  map X Y := fullReplacedMap X.val Y.val
  map_id X := fullCompatibleIdentity_replacedMap X.val
  map_comp X Y Z := fullCompatibleComposition_replacedMap X.val Y.val Z.val

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
