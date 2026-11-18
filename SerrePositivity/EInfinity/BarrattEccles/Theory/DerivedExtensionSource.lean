module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedExtensionNerve

/-!
# K 平坦な厳密源上での導来係数拡大

## 概要
HA §3.2.2 の導来底変更は、K 平坦な厳密入力の係数拡大と全関手で比較できる。

## 方針
同じ半自由置換の augmentation の全円柱を係数拡大し、各頂点で擬同型を反転する。

## 規約
源の関手が各頂点で K 平坦な複体を取ると仮定する。

## 使われ方
M13 の `baseChange_forget` 欄の複体側の比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory DifferentialGraded SSet
open SerrePositivity.InfinityCategories

open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

set_option maxHeartbeats 800000 in
-- dg nerve の頂点と実際の半自由解像の値を照合する。
/-- K 平坦な入力では元の augmentation の係数拡大も擬同型。 -/
lemma complexExtendedAugmentation_quasiIso (X : Complex S) (hX : complexKFlat S X) :
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionAugmentationHomotopy S)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).toTruncated
    QuasiIso ((closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
      (e.map ((truncation 2).map (complexExtensionNerve f))))) := by
  dsimp only
  rw [complexExtensionNerve_edgeChainMap]
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionAugmentationHomotopy S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).toTruncated
  let P := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue S X
  have hP : complexKFlat S P.val :=
    moduleSemifree_objectwiseKFlat S PUnit.{1} (fun _ _ => complexKFlat_unit S)
      P.property PUnit.unit
  have hsrc : (atVertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).obj 0 = P.val := by
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity S).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := S) X))).obj 0 = _
    rw [_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_vertex]
    rfl
  have hQ : complexKFlat S ((atVertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity S ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).obj 0) := hsrc ▸ hP
  have hq := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionAugmentation_edge_quasiIso S (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)
  exact ScalarExtension.extension_quasiIso_of_kFlat_ends f hQ hX
    ((closedToComplex S).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))

/-- The derived and ordinary scalar extensions agree naturally on any ordinary K-flat source. -/
def derivedInfinityBaseChange_sourceIso {C : SSet.{u + 1}}
    (F : C ⟶ nerve (Complex S)) (hF : ∀ x : C _⦋0⦌,
      complexKFlat S ((atVertex F x).obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f)
      (F ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexBaseChange f) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource T) := by
  let L := F ≫ nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed S) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion S (Complex S)
  let R := complexExtensionNerve f
  let Q := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity T
  let H := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionAugmentationHomotopy S
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H L
  let P := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp K (R ≫ Q)
  have he (x : C _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge P x).toTruncated := by
    let y := atVertex L x
    have hy : y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((atVertex F x).obj 0) := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := S) (D := Complex S)).injective
      rfl
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated
    let e' := e.map ((truncation 2).map R)
    have h : QuasiIso ((closedToComplex T).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e')) := by
      dsimp only [e', e, H, R]
      rw [hy]
      exact complexExtendedAugmentation_quasiIso f _ (hF x)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := e'.map ((truncation 2).map Q)) ?_).mpr
    · exact _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_invertsQuasiIso T e' h
    · change (R ≫ Q).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge =
        (R ≫ Q).app (Opposite.op ⦋1⦌) e.edge
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge H L x]
      rfl
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion ≫ Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionRetractIso T).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f))
      rfl (Category.comp_id _)
  have b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion ≫ Q)
      (F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) := by
    simpa only [Category.assoc] using a.precomp (F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource S)
  refine b.symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy P he) ?_ ?_
  · simp only [L, R, Q, _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource, Category.assoc]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S)), ← derivedInfinityBaseChange_inclusion,
      Category.assoc]
  · change (L ≫ 𝟙 _) ≫ (R ≫ Q) = _
    rw [Category.comp_id]
    change (F ≫ (nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed S) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion S (Complex S))) ≫
      (R ≫ Q) = _
    rw [Category.assoc, ← Category.assoc _ R Q, complexClosedNerve_extension]
    simp only [_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource, Q, Category.assoc]

end SerrePositivity.EInfinity.ComplexLimits
