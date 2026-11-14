module

public import SerrePositivity.KST.Spectra.D3CommonLoopSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareIntervalFamily

/-!
概要：共通 BF 左脚を始点成分に持つ、二つの実 loop 四角形の同じ区間族。
方針：構成した同じ錐比較辺を転置し、両端と固定 cospan 境界を回収する。
規約：始点成分は BF 左脚そのものの一次単体。X 間の自然性を仮定しない。
使われ方：比較射と実 loop 図式を同時に保持する d3b② の指定境界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonLoopIntervalSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonLoopIntervalHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ錐比較辺からの全四角形の実区間族。 -/
def commonLoopSquareInterval (X : OmegaSpectrum.{u}) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj Sp :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareIntervalFamily (commonLoopConeEdge X)

lemma commonLoopSquareInterval_source (X : OmegaSpectrum.{u}) :
    commonLoopSquareInterval X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = (loopSourceSquare X).square :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareIntervalFamily_source (commonLoopConeEdge X)

lemma commonLoopSquareInterval_target (X : OmegaSpectrum.{u}) :
    commonLoopSquareInterval X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = (commonLoopSquare X).square :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareIntervalFamily_target (commonLoopConeEdge X)

/-- 全四角形比較の始点辺は、同じ元の共通 BF 左脚に厳密一致。 -/
lemma commonLoopSquareInterval_sourceEdge (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (commonLoopSquareInterval X) 0 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (commonLoopInclusion X)).edge :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareIntervalFamily_sourceEdge (commonLoopConeEdge X)).trans
    (commonLoopConeEdge_projection X)

/-- cospan の三頂点では同じ元の定値区間を保つ。 -/
lemma commonLoopSquareInterval_boundary (X : OmegaSpectrum.{u})
    (k : (horn 2 2 : SSet.{u + 1}) _⦋0⦌) :
    (commonLoopSquareInterval X).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const ((BasedLoop.diagram (tail X)).app (Opposite.op ⦋0⦌) k) :
        (Δ[1] : SSet.{u + 1}) ⟶ Sp) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareIntervalFamily_boundary (commonLoopConeEdge X) k

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
