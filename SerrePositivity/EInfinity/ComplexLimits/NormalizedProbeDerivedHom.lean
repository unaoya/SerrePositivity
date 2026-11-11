module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedKProjectiveDerivedHom
public import SerrePositivity.EInfinity.ComplexLimits.ProbeKProjectiveValues
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeTargetReplacement
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PinchedActionEquivalences

/-!
# 同じ probe の正規化 Hom と既存 D(R) の実 Hom の弱比較

概要：同じ標的置換を中間項とし、正規化 probe Hom を既存 D(R) の Hom へ送る。
方針：K-projective 導来源の実 Hom 比較と、同じ半自由 retract の後合成を使う。
規約：既存の分解値・元の probe・実比較射を保つ。
使われ方：標準 source frame と同じ D(R) 値の写像空間への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories


open scoped Simplicial
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedHomMap (X Y : Complex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (framedLimitKProjectiveProbe A X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y)) :=
  normalizedKProjectiveDerivedHomMap A
    (framedLimitKProjectiveProbe A X) (semifreeKProjectiveTarget A Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose _
        ((complexSemifreeResolutionRetractIso A).app
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y))).hom

open SSet.modelCategoryQuillen in
lemma normalizedProbeDerivedHomMap_homotopyEquivalence (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (normalizedProbeDerivedHomMap A X Y) := by
  let Q := framedLimitKProjectiveProbe A X
  let T := semifreeKProjectiveTarget A Y
  have : KanComplex (SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A Q.val)).obj T.val)) :=
    HomotopicalAlgebra.isFibrant_of_fibration (normalizedKProjectiveHomIso A Q T).hom
  exact (normalizedKProjectiveDerivedHomMap_homotopyEquivalence A Q T).comp
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPostcompose_isQCatEquivalence_of_isIso
      ((complexSemifreeResolutionRetractIso A).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y))).hom
      _).isSimplicialHomotopyEquivalence

end SerrePositivity.EInfinity.ComplexLimits
