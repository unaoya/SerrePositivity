module

public import SerrePositivity.KST.NonConnective.SequentialCandidateLegs
public import SerrePositivity.KST.Spectra.ComponentHomotopyMaps
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.HomOrdinary
public import SerrePositivity.InfinityCategories.F2.CatFunctorCoreIso

/-!
概要：実際の Sp 辺のホモトピー類の等号を、全整数 π への同じ作用へ移す。
方針：coherent Hom 比較の π₀ 単射性から BF 写像空間の成分を回収する。
規約：実際の BF 射の整数 π で計算し、比較を定義だけで済ませない。
使われ方：同じ BF 候補の実余極限余錐の脚の π_* の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialEdgePiSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialEdgePiHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ hSp 射を表す BF 射は、全整数次数で同じ誘導準同型を持つ。 -/
lemma sequentialHomotopyMap_eq_of_homMk_eq {X Y : OmegaSpectrum.{u}} {f g : X ⟶ Y}
    (h : SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated) (j : ℤ) :
    OmegaSpectrum.homotopyMap f j = OmegaSpectrum.homotopyMap g j := by
  let a := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y f)
  let b := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y g)
  have hf : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ a) = (coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary f
  have hg : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ b) = (coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary g
  have hp : SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk a) =
      SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk b) := by
    apply pinchedHomPiZeroToHom_injective (coherentNerveVertex X) (coherentNerveVertex Y)
    change SSet.Truncated.HomotopyCategory.homMk
      (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ a)) =
      SSet.Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ b))
    rwa [hf, hg]
  have hp :=
    (coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective.injective hp
  have hq := congrArg (F2.coherentUliftPiZeroDown (SimplicialCategory.sHom X Y)) hp
  simp only [F2.coherentUliftPiZeroDown, SSet.π₀.lift_mk, a, b] at hq
  change SSet.π₀.mk ((SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (OmegaSpectrum.vertexOfHom f))) =
    SSet.π₀.mk ((SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (OmegaSpectrum.vertexOfHom g))) at hq
  simp only [Equiv.apply_symm_apply] at hq
  change SSet.π₀.mk (OmegaSpectrum.vertexOfHom f) =
    SSet.π₀.mk (OmegaSpectrum.vertexOfHom g) at hq
  apply OmegaSpectrum.homotopyMap_eq_of_levelComponent f g
  intro n
  have hn := congrArg (SSet.mapπ₀ (OmegaSpectrum.evaluation X Y n)) hq
  simpa only [mapπ₀_mk, OmegaSpectrum.vertexOfHom_evaluation,
    PointedMapping.componentOf, PointedMapping.familyVertex_eq_pointedHomVertex] using hn

/-- 同じ実余極限余錐の実辺から読み戻す BF 射。 -/
def sequentialCandidateColimitLegHom (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    D.obj a ⟶ sequentialSpectrum D := coherentNerveEdgeToHom (sequentialCandidateColimitLeg D a)

/-- 実際の余極限余錐の各辺の全整数 π への作用は、既存の同じ注入の作用。 -/
theorem sequentialCandidateColimitLeg_pi (D : SpectrumSequence.{u})
    (a : SequentialIndex.{u}) (j : ℤ) :
    OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D a) j =
      OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection D a) j := by
  apply sequentialHomotopyMap_eq_of_homMk_eq
  rw [sequentialCandidateColimitLegHom, coherentNerveEdge_hom]
  exact sequentialCandidateColimitLeg_hom_eq D a

end SerrePositivity.KST.NonConnective
