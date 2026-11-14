module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKPointSection
public import SerrePositivity.KST.Spectra.SpectrumCircleBKNativeComparison
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.CoherentConeSourceWeightedRestriction

/-!
概要：円 cotensor を頂点とする錐全体の Hom の族の制限は、元の反転 BK 比較族に一致する。
方針：元の錐の weighted な切断を代入し、零単体と単位の点表示を全次数で照合する。
規約：錐全体と元の射そのものの一致。使われ方：実際の円 cotensor 錐の native な極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleSourceRestrictionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の錐全体の全 Hom 族の制限は、元の反転 BK 点の比較族そのもの。 -/
lemma circleBKCoherentConeSourceFamily_restrict (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (circleBKCoherentCone Y)
        (cotensor PointedSimplicialSet.circle Y) (circleBKCoherentCone_vertex Y) X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction (circleBKCoherentCone Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
        circleBKNativeConeComparison X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_restriction_weighted (pointLoopDiagram Y) _ _ _
    (circleBKConeWeightedPointSection Y) (circleBKCoherentCone_cosliceSection_weighted Y)]
  rw [circleBKNativeConeComparison_uncurry]
  simp only [← Category.assoc]
  congr 1
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  change (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor)).app (Opposite.op ⦋n⦌)
          (((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).1.down,
            ((circleBKLiftedEndPoint Y).app (Opposite.op ⦋n⦌)
              ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).2).down)), s) =
    (ULift.up
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor)).app (Opposite.op ⦋n⦌)
          (σ.down, (circleBKReflectedEndPointMap Y).app (Opposite.op ⦋n⦌) PUnit.unit)), s)
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id
      (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))
        (Δ[0] : SSet.{u + 1}))) (Opposite.op ⦋n⦌)) σ
  change ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).1 = σ at hf
  rw [hf]
  congr 3
  have hp : circleBKReflectedEndPointMap Y =
      (SSet.unitHomEquiv _).symm (circleBKReflectedEndPoint Y) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [hp]
  simp only [circleBKLiftedEndPoint, SSet.yonedaEquiv_symm_zero]
  congr 1

end SerrePositivity.KST.Spectra.OmegaSpectrum
