module

public import SerrePositivity.KST.Spectra.D3ComparisonOutput
public import SerrePositivity.KST.Spectra.SpectrumTailEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：B の全関手比較を明示入力として、元の nativeLoop の同値性を回収する。
方針：元の包含同型と B を合成し、共通 BF 射影と nativeTail の実同値を消去する。
規約：B の存在は主張しない。段別・頂点別の比較を全関手比較で代用しない。
使われ方：Sp-2b d3c と、B 到着後の安定性への接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open AdjointLoopRelativeBF
local instance tailLoopSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance tailLoopHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：B を明示入力に取る d3c。元の nativeLoop そのものの同値性。
方針：包含と B の合成から同値を移し、射影と tail 同値の合成を左消去する。
規約：B の存在を証明したとは扱わない。
使われ方：D の一般安定性判定への hΩ の供給。 -/
theorem nativeLoop_isQCatEquivalence_of_tailComparison (hB : NativeLoopComparison.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence nativeLoop.{u} := by
  have h := commonOriginalInfinityEquivalence.{u}.isQCatEquivalence.ofFunctorIso
    (commonInclusionFunctorIso ≪≫ hB)
  have htail : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence nativeTail.{u} := nativeTailEquivalence.isQCatEquivalence
  have hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence commonNativeLoopEndpoint.{u} :=
    commonOriginalInfinityEquivalence.isQCatEquivalence.comp htail
  exact hbase.cancel_left h

end SerrePositivity.KST.Spectra.OmegaSpectrum
