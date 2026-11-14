module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFFiberComparison

/-!
概要：同じ未完備実列の一回の S• 比較から、元の実 fiber 比較の非負次数だけを検出する。
方針：同じ BF 第一正段の評価辺を使い、許される同じ第一段で整数 π を読む。
規約：全段の Sp 引き戻し性は仮定しない。有限 BF 供給と一回の未完備 S• 比較に条件付き。
使われ方：採用済みの連結 fibration から同じ cone の固定 K 構造辺への主経路。
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
local instance nativeBFOneStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)

/-- 概要：元の実 fiber 比較の始点は同じ未完備実核 K の指定頂点。
方針：元の全錐の左下頂点と同じ BF 下辺の始点を回収する。
規約：同じ元の実核と比較辺を保持する。
使われ方：元の構造辺の始点の厳密照合。 -/
theorem dgKappaNativeBFFiberComparison_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeBFSquare R D I hBF)).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeKernelCategory R D I))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ dgKappaNativeBFSquare R D I hBF)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact dgKappaNativeBFSquare_source R D I hBF

/-- 概要：同じ実錐比較の標的は元の実 fiber の指定頂点。
方針：元の錐四角形の左下評価と同じ錐頂点の回収式を使う。
規約：同じ実極限錐を保持する。
使われ方：実比較辺の標的の厳密照合。 -/
theorem dgKappaNativeBFFiberComparison_target :
    (dgKappaNativeBFKLimitCone R D I hBF).vertex =
      (dgKappaNativeBFCanonicalFiberSquare R D I hBF).fiber := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (dgKappaNativeBFKLimitCone R D I hBF))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgKappaNativeBFSquare R D I hBF)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{max (u + 1) v})
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{max (u + 1) v + 1}) ⊗ Δ[1])) 0 0)).app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap _).app (Opposite.op ⦋0⦌)
      (dgKappaNativeBFKLimitCone R D I hBF)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex] at h
  exact h.symm

/-- 概要：同じ未完備実核 K から元の実 fiber への全比較辺。
方針：同じ錐比較の始点表示だけを元の実核へ戻す。
規約：比較辺の全一単体と同じ元の実 fiber を保持する。
使われ方：一回の S• fibration の非負次数比較。 -/
def dgKappaNativeBFFiberVertexComparison : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
    (dgKappaNativeBFCanonicalFiberSquare R D I hBF).fiber :=
  (SSet.Edge.ofTruncated (dgKappaNativeBFFiberComparison R D I hBF)).ofEq
    (dgKappaNativeBFFiberComparison_source R D I hBF)
    (dgKappaNativeBFFiberComparison_target R D I hBF)

/-- 概要：一回の元の S• 比較に条件付きで、同じ実 fiber 比較は非負次数 π 同型。
方針：同じ第一正段の評価の可逆性を、整数 π の同じ第一段表示へ反映する。
規約：全正段の引き戻し性や完備化後の Sp 引き戻し性は仮定しない。
使われ方：K-7 c5・d3 の採用済み連結経路。 -/
theorem dgKappaNativeBFFiberVertexComparison_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFFiberVertexComparison R D I hBF).toTruncated) j) := by
  let e := dgKappaNativeBFFiberVertexComparison R D I hBF
  let f := SpectrumHo.edgeMap e
  have hs := dgKappaNativeBFFiberComparison_spaceEvaluation_isInvertible R D I hBF 1
    (dgKappaNativeBF_spaceEvaluation_isPullback R D I hBF 0 hS)
  have hes : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      (e.toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v}) (e := e.toTruncated.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1))))
      (f := (dgKappaNativeBFFiberComparison R D I hBF).map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) rfl).mpr hs
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} 1)))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v}) (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
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
