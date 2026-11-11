module

public import SerrePositivity.KST.Spectra.SpectrumCircleLoopDiagramEvaluation
public import SerrePositivity.KST.Spectra.SpectrumCotensorFullFaithfulnessCriterion

/-!
概要：元の native loop 関手と元の円 cotensor 関手を、高次単体を含む関手同型で比較する。
方針：同じ終点の全 loop 図式族を比較し、両始点を評価して終点の共通解像を消去する。
規約：全関手単体集合内の同型。使われ方：loop の完全忠実性と一段移動の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の円の全 loop 図式族は、同じ終点上で native な選択族全体と同型。 -/
def circleLoopDiagramFamilyIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso circleLoopDiagramFamily.{u}
      (((CotensorCompatible.sourceInfinityEquivalence PointedSimplicialSet.circle).inv ≫
        CotensorCompatible.sourceInfinityMap PointedSimplicialSet.circle) ≫
          nativeLoopTargetEquivalence.inv) := by
  apply nativeLoopDiagramFamilyIso
  rw [Category.assoc, nativeLoopTargetEquivalence_inv_target, Category.comp_id,
    circleLoopDiagramFamily_target]

/-- 元の円 cotensor と元の native loop は、全ての高次単体に自然に同型。 -/
def nativeLoopCircleFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nativeCotensor PointedSimplicialSet.circle.{u}) nativeLoop.{u} := by
  have hs := circleLoopDiagramFamilyIso.{u}.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
  rw [circleLoopDiagramFamily_source, Category.assoc] at hs
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nativeCotensor PointedSimplicialSet.circle)
    (((CotensorCompatible.sourceInfinityEquivalence PointedSimplicialSet.circle).inv ≫
      CotensorCompatible.sourceInfinityMap PointedSimplicialSet.circle) ≫ nativeLoop) at hs
  have ht := circleLoopDiagramFamily_targetIso.{u}.postcomp nativeLoop
  rw [circleLoopDiagramFamily_target, Category.id_comp] at ht
  exact hs ≪≫ ht

local instance nativeLoopCircleEvaluationKan (X Y : OmegaSpectrum.{u}) :
    KanComplex ((CategoryTheory.ihom PointedSimplicialSet.circle.{u}).obj
      (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle X)
        Y.toKanSequence)).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の native loop の完全忠実性は、元の円の普遍評価の全 Hom の同値性と同値。 -/
lemma nativeLoop_isFullyFaithful_iff_evaluationPost :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful nativeLoop.{u} ↔ ∀ X Y : OmegaSpectrum.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
        (CotensorCompatible.evaluationPost PointedSimplicialSet.circle X Y).right :=
  nativeLoopCircleFunctorIso.isFullyFaithful_iff.symm.trans
    (nativeCotensor_isFullyFaithful_iff PointedSimplicialSet.circle)

end SerrePositivity.KST.Spectra.OmegaSpectrum
