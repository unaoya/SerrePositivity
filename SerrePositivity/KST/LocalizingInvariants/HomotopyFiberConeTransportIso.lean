module

public import SerrePositivity.KST.LocalizingInvariants.ReplacedFiberConeComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowInverseControl

/-!
概要：任意射の homotopy fiber 錐から fibration 置換の錐への指定比較を、全図式同型にする。
方針：保存済みホモトピーの全頂点での可逆性を使い、頂点の定値辺を回収する。
規約：fibration 置換単位の元の prism を保持。使われ方：fiber 比較の任意射への全図式移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance fiberTransportSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance fiberTransportNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y)

def homotopyFiberConeTransportIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Y := Sp.{u}) (homotopyFiberCone p).val
    (replacedCone (fibrationReplacementProjection p)).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (homotopyFiberTransport p).homotopy
    (homotopyFiberTransport p).vertical_isInvertible

lemma homotopyFiberConeTransportIso_apex :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (X := Sp.{u}) (homotopyFiberConeTransportIso p).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)) = Arrow.mk (𝟙 (SpectrumHo.obj (homotopyFiber p))) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (homotopyFiberTransport p).homotopy)) _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  have he := StrictConeTransport.apexEdge (CospanReplacement.unit p (fromPoint Y))
    (CospanReplacement.unit_isInvertible p (fromPoint Y))
    (replacedCone (fibrationReplacementProjection p))
    (replacedCone_isLimit (fibrationReplacementProjection p))
  have he' := he.trans (congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)
    (replacedCone_vertex (fibrationReplacementProjection p)))
  have hi : (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber p))).toTruncated =
      Truncated.Edge.id (X := (truncation 2).obj Sp.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber p)) := SSet.Edge.toTruncated_id _
  have ha := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (homotopyFiberTransport p).homotopy)
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber p))).toTruncated
    (he'.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _))
  rw [hi, Truncated.HomotopyCategory.homMk_id] at ha
  refine (Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopyFiberTransport p).homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.joinApexVertex _)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (homotopyFiberTransport p).homotopy) ?_).trans ha
  have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) := by
    apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  exact congrArg (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopyFiberTransport p).homotopy
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _).app (Opposite.op ⦋0⦌) v)).edge) hv

end SerrePositivity.KST.LocalizingInvariants.FiberModel
