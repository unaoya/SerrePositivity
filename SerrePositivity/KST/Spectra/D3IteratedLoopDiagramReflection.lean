module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointJointFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationSquares

/-!
概要：自明 Kan 射影による認証から、同じ loop 図式圏内の loop 性を反映する。
方針：二つの零角と実引き戻し四角形を、同じ終点射影で同時に反映する。
規約：図式・単位・比較を変更しない。使われ方：実四次元図式の反復 loop 認証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 同じ全四角形の loop 性は、自明 Kan 射影の下で保存され反映される。 -/
lemma d3IsLoopDiagramVertex_iff_trivialKan_image {E B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    (v : ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj E) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex v ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q).app _ v) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
  rw [OmegaSpectrum.AdjointLoopRelativeBF.d3SquareDiagram_postcomp]
  exact and_congr
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration q _)
    (and_congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration q _)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_iff_postcomp_trivialKanFibration q _))

end SerrePositivity.KST.Spectra
