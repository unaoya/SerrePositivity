module
public import SerrePositivity.KST.Fibration.KanForgetDetection
public import SerrePositivity.KST.Fibration.PositiveKanEvaluationDetection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomNaturality

/-! # 同じ元のスペクトル段評価の基点忘却と、全正段による可逆性検出 -/

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

local instance spaceEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ元の BF 段評価の基点を忘れ、全 Hom を保持する。 -/
def spectrumSpaceEvaluation (n : ℕ) :
    EnrichedFunctor SSet.{u} OmegaSpectrum.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (spectrumKanEvaluation n).comp SSet pointedKanForgetEnriched

/-- 同じ段の通常の Kan 値評価。 -/
abbrev spectrumSpaceEvaluationOrdinary (n : ℕ) : OmegaSpectrum.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (spectrumSpaceEvaluation n)

/-- 全 Hom 作用は、元の app n の基礎射の豊穣表示を回収する。 -/
theorem spectrumSpaceEvaluation_hom {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    eHomEquiv SSet f ≫ (spectrumSpaceEvaluation n).map X Y =
      eHomEquiv SSet (show (spectrumSpaceEvaluation n).obj X ⟶
        (spectrumSpaceEvaluation n).obj Y from (f.app n).right) := by
  have hm := congrArg (eHomEquiv SSet) (spectrumKanEvaluationOrdinary_map n f)
  change eHomEquiv SSet ((eHomEquiv SSet).symm
    (eHomEquiv SSet f ≫ (spectrumKanEvaluation n).map X Y)) = _ at hm
  rw [Equiv.apply_symm_apply] at hm
  change eHomEquiv SSet f ≫ ((spectrumKanEvaluation n).map X Y ≫ _) = _
  rw [← Category.assoc, hm]
  exact pointedClosedHomInclusion_hom (f.app n)

/-- 元の coherent 段評価を基点忘却すると、元の基礎射の同じ一単体になる。 -/
theorem spectrumSpaceEvaluation_edge {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (spectrumSpaceEvaluation n).obj X ⟶
        (spectrumSpaceEvaluation n).obj Y from (f.app n).right)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ _ _ (spectrumSpaceEvaluation_hom f n)

/-- 元の通常の段評価は、同じ app n の基礎射そのもの。 -/
theorem spectrumSpaceEvaluationOrdinary_map {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    (spectrumSpaceEvaluationOrdinary n).map f = (f.app n).right := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (spectrumSpaceEvaluation n) f = (f.app n).right
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_of_hom
  exact spectrumSpaceEvaluation_hom f n

/-- Kan 性だけを忘れると、同じ元の段評価の基点忘却と一致する。 -/
theorem spectrumSpaceEvaluationOrdinary_forget (n : ℕ) :
    spectrumSpaceEvaluationOrdinary.{u} n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n ⋙ PointedSimplicialSet.forget := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact spectrumSpaceEvaluationOrdinary_map f n

/-- 同じ基点忘却後の段評価が可逆なら、同じ点つき段評価も可逆。 -/
theorem spectrumSpaceEvaluation_reflects_pointed {X Y : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := PointedKanInfinity.{u}) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)))) := by
  let g : (spectrumKanEvaluation n).obj X ⟶ (spectrumKanEvaluation n).obj Y :=
    ObjectProperty.homMk (f.app n)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (spectrumSpaceEvaluation n).obj X ⟶
        (spectrumSpaceEvaluation n).obj Y from (f.app n).right)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))))
      (spectrumSpaceEvaluation_edge f n)).mp hf
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) :=
    pointedKanObject_edge_isInvertible_of_piIsomorphism g
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanMap_piIsomorphism_of_invertible
        (X := (spectrumSpaceEvaluation n).obj X) (Y := (spectrumSpaceEvaluation n).obj Y)
        (f.app n).right hi)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := PointedKanInfinity.{u})
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated) (spectrumKanEvaluation_edge f n)).mpr hg

/-- 全正段の基点忘却後の可逆性は、同じ元の Sp 辺の可逆性を検出する。 -/
theorem spectrumEdge_isInvertible_of_positive_spaceEvaluation {x y : Sp.{u} _⦋0⦌}
    (e : Sp.{u}.Edge x y)
    (he : ∀ r : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (e.toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1)))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Sp.{u}) e.toTruncated := by
  have hf : OmegaSpectrum.PiIsomorphism (SpectrumHo.edgeMap e) := by
    apply spectrum_piIsomorphism_of_positive_evaluation
    intro r
    apply spectrumSpaceEvaluation_reflects_pointed
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (f := e.toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1)))))
      (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1))).app
        (Opposite.op ⦋1⦌)) (SpectrumHo.edgeMap_edge e))).mpr
    exact he r
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Sp.{u})
    (f := e.toTruncated) (SpectrumHo.edgeMap_edge e)).mp
    (OmegaSpectrum.isInvertible_of_piIsomorphism _ hf)

end SerrePositivity.KST.Fibration
