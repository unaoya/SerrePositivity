module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFFiberComparison

/-!
概要：実供給 BF 四角形の同じ fiber 比較へ、一回の S• fibration を渡す。
方針：同じ第一正段の可逆性を非負整数 π の表示へ反映する。
規約：hBF の存在仮定や旧 BF 四対象との等号は使わない。
使われ方：K-6 c5 と K-7 c5・d3 の実供給側の非負次数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFOneStageCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：一回の元の S• 比較に条件付きで、実供給四角形の同じ実 fiber 比較は非負次数 π 同型。
方針：同じ第一正段の評価の可逆性を、整数 π の同じ第一段表示へ反映する。
規約：全正段の引き戻し性や完備化後の Sp 引き戻し性は仮定しない。
使われ方：K-7 c5・d3 の採用済み連結経路。 -/
theorem dgKappaSuppliedBFFiberComparison_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j) := by
  let e := SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)
  let f := SpectrumHo.edgeMap e
  have hs := dgKappaSuppliedBFFiberComparison_spaceEvaluation_isInvertible R D I 1
    (dgKappaSuppliedBF_spaceEvaluation_isPullback R D I 0 hS)
  have hes : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      (e.toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      (e := e.toTruncated.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1))))
      (f := (dgKappaSuppliedBFFiberComparison R D I).map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) rfl).mpr hs
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1))))
      (f := e.toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) (congrArg
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)).app (Opposite.op ⦋1⦌))
      (SpectrumHo.edgeMap_edge e))).mpr
    exact hes
  rw [SpectrumHo.piMap_edge]
  apply (OmegaSpectrum.homotopyMap_bijective_iff_levelMap f j 1 (by omega)).mpr
  exact spectrum_levelMap_bijective_of_evaluation f 1
    (spectrumSpaceEvaluation_reflects_pointed f 1 hf) _

end SerrePositivity.KST.NonConnective
