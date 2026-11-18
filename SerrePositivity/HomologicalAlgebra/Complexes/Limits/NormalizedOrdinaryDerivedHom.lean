module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeDerivedSpan
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DerivedSourceValues
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProbeDerivedSourceVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport

/-!
# 元の通常導来源の同じ端点を持つ実正規化 Hom 比較

概要：probe の実 D(R) Hom 比較を、元の X,Y の通常導来源の値へ戻す。
方針：実値の等式と元の probe 比較の全関手同型を使う。
規約：元の導来単位の構成と同じ始域比較の逆を前合成する。
使われ方：元の単位誘導射と同じ ∞ 写像空間 Hom span の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories


open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedEndpointIso (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y)) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)))
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
    ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource_vertex_eq A (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X)).trans
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_vertex_eq A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)).symm)
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_vertex_eq A Y).symm

def normalizedOrdinaryDerivedHomMap (X Y : Complex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  _root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedHomMap A X Y ≫ (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedEndpointIso A X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose _
      (_root_.SerrePositivity.ComplexLimits.complexProbeDerivedSourceVertexIso A X).inv

open _root_.SSet.modelCategoryQuillen in
lemma normalizedOrdinaryDerivedHomMap_homotopyEquivalence (X Y : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.ComplexLimits.normalizedOrdinaryDerivedHomMap A X Y) := by
  have : KanComplex (SSet.uliftFunctor.{u + 1, u}.obj
      (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y).val)) :=
    _root_.HomotopicalAlgebra.isFibrant_of_fibration
      (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X)
        (_root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A Y)).hom
  have h₀ := _root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedHomMap_homotopyEquivalence A X Y
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedEndpointIso A X Y)
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedPrecompose_isQCatEquivalence_of_isIso
    (_root_.SerrePositivity.ComplexLimits.complexProbeDerivedSourceVertexIso A X).inv
    ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))).isSimplicialHomotopyEquivalence
  exact h₀.comp (h₁.comp h₂)

end SerrePositivity.ComplexLimits
