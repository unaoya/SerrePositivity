module

public import SerrePositivity.KST.Spectra.D3CommonLoopDiagramSection

/-!
概要：Sp-2 の B から Sp-2b の d3c・d3d へ渡す全関手比較の出力型を固定する。
方針：元の共通 refined 関手、厳密 tail 終点、nativeLoop を同じ型へ明示する。
規約：出力型の公開は、その inhabitant の供給ではない。未完成の B を仮定なしの値としない。
使われ方：Sp-2b は NativeLoopComparison を明示引数として後段を先行構成する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3OutputSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 共通 refined 関手から元の nativeLoop への、B が実際に供給すべき全関手同型の型。 -/
abbrev NativeLoopComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched.{u})
    (commonNativeLoopEndpoint ≫ nativeLoop)

/-- 選択済み実 loop 全図式の始点までの比較。ここに未証明の B の本体が残る。 -/
abbrev ChosenLoopSourceComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched.{u}) commonChosenLoopSource

/-- 実始点までの比較が供給されたとき、元の指定 nativeLoop 比較へ接続する。 -/
def nativeLoopComparisonOfChosenSource (hB : ChosenLoopSourceComparison.{u}) :
    NativeLoopComparison.{u} := hB ≪≫ commonChosenLoopSourceNativeIso

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
