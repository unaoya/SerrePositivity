module

public import SerrePositivity.EInfinity.PowerOperation.OmegaSequenceReplacementFunctor
public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
# Ω 列の通常の nerve から native Sp への比較

BF 1978 §2 の同じ単射置換と、Kerodon Remark 3.1.6.3 の通常の nerve の
coherent nerve への標準射を合成する。一般の coherent 図式の厳密化は主張しない。
［一般∞］移動候補。D(k) からの V の完成とは別の部品。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open scoped Simplicial

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- Ω 列の厳密な通常の図式を、同じ置換を持つ native Sp の図式へ送る。 -/
def omegaSequenceNative : nerve KanOmegaSequence.{u} ⟶ Sp.{u} :=
  nerveMap omegaSequenceReplacementFunctor ≫ nerveToCoherent OmegaSpectrum.{u}

/-- 頂点の対象は、同じ指定された単射置換のスペクトルである。 -/
lemma omegaSequenceNative_vertex (X : KanOmegaSequence.{u}) :
    omegaSequenceNative.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) =
      coherentNerveVertex (omegaSequenceReplacementFunctor.obj X) := by
  change (nerveToCoherent OmegaSpectrum.{u}).app (Opposite.op ⦋0⦌)
    ((nerveMap omegaSequenceReplacementFunctor).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X)) = _
  rw [nerveMap_app_mk₀]
  exact nerveToCoherent_vertex _

end SerrePositivity.EInfinity.PowerOperation
