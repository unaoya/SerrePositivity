module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeSliceEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismFamilyComposition

/-!
概要：元の大域 cone 族と同じ実 slice 評価族の合成は、全関手圏で恒等となる。
方針：同じ slice prism の両端・全射影を既存の全族の合成定理へ代入する。
規約：HA Construction 1.3.1.6・1.3.1.13、通常 augmentation の円柱との同定は未主張。使われ方：元の augmentation 逆との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)


open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof

private lemma sliceTriangleFromPrism {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    {f : K ⟶ T} (l : SSet.Homotopy (SSet.const z) f)
    (t : SSet.Homotopy f (SSet.const z))
    (a : K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (hb : prismEndpoint 0 K ≫ p = SSet.const (sliceIdentityCone z))
    (ht : prismEndpoint 1 K ≫ p = a)
    (hl : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p ≫
      sliceOverProjection (SSet.yonedaEquiv.symm z) = l.h)
    (he : t.h = (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry a) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy t) =
      𝟙 (SSet.HomotopyCategory.mk (functorVertex (SSet.const (X := K) z))) := by
  let r := functorHomotopyRefl (SSet.const (X := K) z)
  have hb' : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry (prismEndpoint 0 K ≫ p) = r.h := by
    rw [hb, ← roofSliceEvaluationHomotopy_precomp_h,
      roofSliceEvaluationHomotopy_const_identity_h]
    exact (SSet.comp_const _ z).symm
  have ht' : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry (prismEndpoint 1 K ≫ p) = t.h :=
    (congrArg (fun q : K ⟶ sliceOver (SSet.yonedaEquiv.symm z) =>
      (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
        sliceOverUncurry q) ht).trans he.symm
  exact (slicePrismFamily_comp z l r t p hb' ht' hl).trans
    (functorHomotopyRefl_hom (SSet.const (X := K) z))

lemma strictRawModuleTensorDoubleConeSliceEvaluation_triangle :
    strictRawModuleTensorConeFamilyHom A X P Q ≫ strictRawModuleTensorDoubleConeSliceEvaluationHom A X P Q =
      𝟙 (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := nerve (strictRawModuleTensorElementIndex A X P Q))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))))) := by
  let K := nerve (strictRawModuleTensorElementIndex A X P Q)
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
  exact sliceTriangleFromPrism z (strictRawModuleTensorConeHomotopy A X P Q)
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q)
    (strictRawModuleTensorDoubleConeOverDiagram A X P Q)
    (strictRawModuleTensorDoubleConeSlicePrism A X P Q)
    (strictRawModuleTensorDoubleConeSlicePrism_zero A X P Q)
    (strictRawModuleTensorDoubleConeSlicePrism_one A X P Q)
    (by
      exact congrArg (fun q => (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ q)
        (strictRawModuleTensorDoubleConeSlicePrism_projection A X P Q))
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h A X P Q)

end SerrePositivity.EInfinity.BarrattEccles
