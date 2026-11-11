module
public import SerrePositivity.KST.Fibration.SpectrumKanEvaluationOrdinary
public import SerrePositivity.KST.Fibration.PointedKanInvertiblePi
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-! # 同じ全正段での coherent 可逆性は、元の Sp 辺の可逆性を検出する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance positiveDetectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の BF 射の coherent な段評価は、同じ app n の一単体そのもの。 -/
theorem spectrumKanEvaluation_edge {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (ObjectProperty.homMk (f.app n) :
          (spectrumKanEvaluation n).obj X ⟶ (spectrumKanEvaluation n).obj Y)).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv
  have hm := congrArg (eHomEquiv SSet) (spectrumKanEvaluationOrdinary_map n f)
  change eHomEquiv SSet ((eHomEquiv SSet).symm
    (eHomEquiv SSet f ≫ (spectrumKanEvaluation n).map X Y)) = _ at hm
  rwa [Equiv.apply_symm_apply] at hm

/-- 同じ coherent 段評価の可逆性は、元の app n の全 π を同型にする。 -/
theorem spectrum_levelMap_bijective_of_evaluation {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{u})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))))) (k : ℕ) :
    Function.Bijective (OmegaSpectrum.levelMap f n k) := by
  let g : (spectrumKanEvaluation n).obj X ⟶ (spectrumKanEvaluation n).obj Y :=
    ObjectProperty.homMk (f.app n)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := PointedKanInfinity.{u})
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated) (spectrumKanEvaluation_edge f n)).mp hf
  exact pointedKan_pi_bijective_of_invertible g hi k

/-- 全正段で元の coherent 辺が可逆なら、同じ BF 射は整数 π 同値。 -/
theorem spectrum_piIsomorphism_of_positive_evaluation {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y)
    (hf : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{u})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)))))) :
    OmegaSpectrum.PiIsomorphism f := by
  intro j
  rw [OmegaSpectrum.homotopyMap_eq_levelMap]
  exact spectrum_levelMap_bijective_of_evaluation f (j.natAbs + 1) (hf j.natAbs) _

/-- 任意の元の Sp 辺の可逆性は、同じ全正段の像で検出できる。 -/
theorem spectrumEdge_isInvertible_of_positive_evaluation {x y : Sp.{u} _⦋0⦌}
    (e : Sp.{u}.Edge x y)
    (he : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{u}) (e.toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Sp.{u}) e.toTruncated := by
  have hf : OmegaSpectrum.PiIsomorphism (SpectrumHo.edgeMap e) := by
    apply spectrum_piIsomorphism_of_positive_evaluation
    intro r
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := PointedKanInfinity.{u})
      (f := e.toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)))))
      (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))).app
        (Opposite.op ⦋1⦌)) (SpectrumHo.edgeMap_edge e))).mpr
    exact he r
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Sp.{u})
    (f := e.toTruncated) (SpectrumHo.edgeMap_edge e)).mp
    (OmegaSpectrum.isInvertible_of_piIsomorphism _ hf)

end SerrePositivity.KST.Fibration
