module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangeTransportWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeRestrictionFirstVertexDiamond
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveRepresentationCartesianSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstVertexBaseChangeIsoAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationRestriction

/-!
概要：元の指定表現比較と底変換比較を、同じ初頂点の全族で照合する。
方針：指定witnessのnerve比較と二経路のnative制限の一致を使い、一般の合成則で戻す。
規約：HTT §3.3.2・Kerodon Tag 028Tの構成の特殊な照合。元の同型を選び直さない。
使われ方：P3-D、初頂点での充満忠実な制限による全体への反映。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations


/-- 指定表現の底変換比較は、同じ初頂点上の全族で元の表現比較と両立する。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定初頂点による特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定表現比較と底変換の初頂点上での全族の一致。"]
lemma leftStraighteningRepresentation_baseChange_firstVertex :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  (leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map lD) ≪≫
    leftStraighteningInfinityDiagram_firstVertexTransportIso q ≪≫
    nerveCoherentTransportRepresentationIso r ((R.nativeRestrict k).nativeRestrict lD) =
  ((leftStraighteningInfinityDiagram_representationIso p R).precomp (U.map k)).precomp
    (U.map lD) := by
  intro E B D hB hD p hp k U lB lD H q p₀ r R
  let d := leftStraighteningBaseChangePullbackData p k
  let t := U.map (nerveMap H)
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict (U.map d.val) t d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let T₀ := (R.nativeRestrict lB).cartesianRestrict (U.map d.val) t d.property.2.2.2
  let T₁ := (R.nativeRestrict k).nativeRestrict lD
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν : FunctorIso (t ≫ leftCoherentTransport p₀) (leftCoherentTransport r) :=
    (θp.precomp t).symm ≪≫ diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  have hb : t ≫ U.map lB = U.map lD ≫ U.map k := by
    simpa only [t, Functor.map_comp] using
      congrArg U.map (transportSimplexFirstVertexMap_naturality k)
  obtain ⟨a, ha⟩ := leftStraighteningBaseChange_transportWitness p k
  have hN := nerveComparison_cartesian_witness p₀ r d.val (nerveMap H) d.property.2.2.2 a
    (R.nativeRestrict lB)
  rw [ha] at hN
  have hT : T₀ = T₁ := nativeRestrict_firstVertex_diamond p k R
  let π := fun (T : LeftTransportRepresentation (U.map r)) => T.diagram
  have hA : diagramIsoCongr rfl (congrArg π hT)
      ((nerveCoherentTransportRepresentationIso p₀ (R.nativeRestrict lB)).precomp t) =
        ν ≪≫ nerveCoherentTransportRepresentationIso r T₁ := by
    exact (congrArg
      (fun z : FunctorIso (t ≫ leftCoherentTransport p₀) T₀.diagram =>
        diagramIsoCongr rfl (congrArg π hT) z) hN).trans
          (diagramIsoCongr_family_comp π
            (fun T => nerveCoherentTransportRepresentationIso r T) hT ν)
  exact firstVertexBaseChange_isoAlgebra (U.map lB) (U.map lD) t (U.map k) hb
    (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) R.diagram
    (leftCoherentTransport p₀) (leftCoherentTransport r) θp θq β
    (leftStraighteningInfinityDiagram_representationIso p R)
    (nerveCoherentTransportRepresentationIso p₀ (R.nativeRestrict lB))
    (nerveCoherentTransportRepresentationIso r T₁)
    (leftStraighteningInfinityDiagram_representationIso_precomp p R) hA

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
