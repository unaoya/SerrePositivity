module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeSlicePrismProjection
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched

/-!
概要：構成した実 slice 図式の普遍評価を、元の frame 図式から同じ X への全族にする。
方針：同じ普遍評価ホモトピーを全図式で制限し、元の射影の等式で始域を合わせる。
規約：HA Construction 1.3.1.6・1.3.1.13、通常 augmentation の円柱との同定は別に検証する。使われ方：大域合成三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma sliceEvaluationEndpointZero {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z))
    (f : K ⟶ T)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z) = f) :
    SSet.ι₀ (X := K) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h = f :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h₀.trans ha

private lemma sliceEvaluationEndpointOne {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    SSet.ι₁ (X := K) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h = SSet.const z :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h₁.trans (SSet.comp_const a z)

def strictRawModuleTensorDoubleConeSliceEvaluationHomotopy :
    SSet.Homotopy (strictRawModuleTensorElementNerveDiagram A X P Q)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
    (strictRawModuleTensorDoubleConeOverDiagram A X P Q)).h
  h₀ := by
    exact sliceEvaluationEndpointZero ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))
      (strictRawModuleTensorDoubleConeOverDiagram A X P Q)
      (strictRawModuleTensorElementNerveDiagram A X P Q)
      (strictRawModuleTensorDoubleConeOverDiagram_projection A X P Q)
  h₁ := by
    exact sliceEvaluationEndpointOne ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))
      (strictRawModuleTensorDoubleConeOverDiagram A X P Q)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

lemma strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h :
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q).h =
      (β_ (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (strictRawModuleTensorDoubleConeOverDiagram A X P Q) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h _ _

def strictRawModuleTensorDoubleConeSliceEvaluationHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (strictRawModuleTensorElementNerveDiagram A X P Q)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q))

end SerrePositivity.EInfinity.BarrattEccles
