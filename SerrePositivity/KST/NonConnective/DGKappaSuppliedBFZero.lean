module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFSquare
public import SerrePositivity.KST.NonConnective.DGKappaNativeConeZero
public import SerrePositivity.KST.Fibration.StableMultiKanTerminal

/-!
概要：同じ未完備 BF 四角形の零角を、全正段の元の S• 図式比較で認証する。
方針：実供給の同じ零角の正段は空間の終対象であり、元の一点射の可逆性を全正段から検出する。
規約：旧 BF 四対象との同一視や hBF の存在仮定は使わない。
使われ方：K-7 c5 の同じ実 fiber と実 loop の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFZeroSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実 BF 零角の各正段は空間の終対象。
方針：同じ元の全 S• 四角形の零角の終対象性を全図式比較の成分で移す。
規約：供給された全四角形比較を使い、対象別同値から自然性を推論しない。
使われ方：同じ元の BF 零角の零性の検出。 -/
theorem dgKappaSuppliedBF_corner_spaceEvaluation_isTerminal (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) 0 1) := by
  have ht := verdierMultiKanSquare_corner_isTerminal r (dgKappaNativeVerdierDiagram R D I)
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1})) 0 1
  exact ht.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (dgKappaSuppliedBFMultiSquareIso R D I r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))

/-- 概要：同じ供給 BF 四角形の零角は、元の一点スペクトルとの実同型で零。
方針：元の一点射の全正段の可逆性を、同じ実 Sp 辺へ反映する。
規約：供給済みの実 BF 四角形を使用。Sp の安定性や K の局所化性は使わない。
使われ方：同じ元の BF 四角形から実 fiber を作る零角。 -/
theorem dgKappaSuppliedBFSquare_zero_corner :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 0 1) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 0 1
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject z
  let f := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from X
  let e : Sp.Edge z (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{max (u + 1) v}) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).ofEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object z) rfl
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
    apply spectrumEdge_isInvertible_of_positive_spaceEvaluation
    intro r
    have hs := dgKappaSuppliedBF_corner_spaceEvaluation_isTerminal R D I r
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanVertex_isTerminal_of_localized_toPoint
      change IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (terminal.from (𝟙_ SSet.{max (u + 1) v})))
      have : IsIso (terminal.from (𝟙_ SSet.{max (u + 1) v})) :=
        isIso_of_isTerminal isTerminalTensorUnit terminalIsTerminal _
      infer_instance
    exact isIso_of_isTerminal hs.isTerminalHo ht.isTerminalHo _
  exact OmegaSpectrum.pointZeroVertex.isZero.of_vertexIso
    (asIso (Truncated.HomotopyCategory.homMk e.toTruncated)).symm

end SerrePositivity.KST.NonConnective
