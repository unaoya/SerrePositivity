module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementForgetFamily
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveElementRoofWeak
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProbeKProjectiveValues
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedPostcompositionFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomLiftIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PinchedActionEquivalences
/-!
概要：元の全要素パラメータから実 U の値への弱な複体屋根族を構成する。
方針：元の複体屋根・標的 augmentation・同じ忘却頂点比較を合成する。
規約：元の全族と実 U の標的を保持する。
使われ方：元の自由単位による Hom 比較の弱同値性を検査する基準射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded

open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：同じ半自由標的から実 U の元の標的への射。
方針：元の augmentation の導来像と元の頂点比較の逆を合成する。
規約：同じ二射を保持。使われ方：基準屋根族の標的輸送。 -/
def freeProbeRelativeTargetHom :
    (HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.obj.carrier).val)) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
    HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)))) :=
  Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.obj.carrier)).map
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated ≫
    (cofibrantForgetOrdinaryVertexIso A B).inv

/-- 概要：同じ標的輸送は実同型。
方針：元の augmentation の擬同型反転と頂点同型の逆を使う。
規約：元の射自身を検証。使われ方：基準全族の弱同値性。 -/
lemma freeProbeRelativeTargetHom_isIso : IsIso (freeProbeRelativeTargetHom A B) := by
  have : IsIso (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.obj.carrier)).map
        (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) :=
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_map_weak A _
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation_quasiIso A B.obj.carrier)
  dsimp only [freeProbeRelativeTargetHom]
  infer_instance

/-- 概要：同じ相対全要素から元の複体屋根を実 U の標的へ送る。
方針：元の Hom 宇宙を戻し、同じ屋根族を指定標的射で後合成する。
規約：同じ全パラメータを保持。使われ方：実単位比較の弱な基準族。 -/
def freeProbeRelativeUnitReference : nerve (freeProbeRelativeElementIndex A X B) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)))
    ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj) ≫
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.obj.carrier).val ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose _ (freeProbeRelativeTargetHom A B)

/-- 概要：元の複体屋根による基準全族自身は弱同値。
方針：元の down 同型・K-projective 屋根・同じ標的同型の作用を合成する。
規約：元の実写像を保持。使われ方：実単位比較の弱同値性の反映。 -/
lemma freeProbeRelativeUnitReference_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeProbeRelativeUnitReference A X B) := by
  have := freeProbeRelativeTargetHom_isIso A B
  let q := (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X))
  have hpost : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose q (freeProbeRelativeTargetHom A B)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPostcompose_isQCatEquivalence_of_isIso
      (freeProbeRelativeTargetHom A B) q).isWeakHomotopyEquivalence
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homLiftIso (freeProbeElementIndex A X B.obj))).isWeakHomotopyEquivalence
  have hr := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap_weak A (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X)
    (_root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A B.obj.carrier)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.obj.carrier).val) at hr
  exact hd.comp (hr.comp hpost)

/-- 概要：同じ基準族の全関手射は元の複体屋根と同じ標的射の合成。
方針：元の屋根族公式と全パラメータの前後合成公式を使う。
規約：点ごとの一致に縮めない。使われ方：元の単位三角形との照合。 -/
lemma freeProbeRelativeUnitReference_family :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeUnitReference A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.obj.carrier).val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve (freeProbeRelativeElementIndex A X B))
        (freeProbeRelativeTargetHom A B) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj) ≫
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.obj.carrier).val) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose _ (freeProbeRelativeTargetHom A B) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) = _
  rw [_root_.SerrePositivity.ComplexLimits.pinchedPostcompose_intervalFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementOrdinaryPinchedMap_family]

end SerrePositivity.EInfinity.BarrattEccles
