module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveDerivedComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyIsoTransport

/-!
# 元の K-projective 複体の正規化テンソル Hom と実 D(R) の Hom

概要：同じ正規化テンソル Hom から、同じ分解値間の既存 D(R) の Hom へ実弱比較を作る。
方針：実 DK 同型と元の dg nerve 上の導来源の充満忠実性を合成する。
規約：同じ二つの複体と同じ実分解関手を保持する。
使われ方：標準 frame Hom span の実 ∞ 写像空間への接続。
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

def normalizedKProjectiveHomIso (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X.val)).obj Y.val) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.ComplexLimits.KProjectiveComplex A))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) := by
  have e : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X.val)).obj Y.val ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) X Y :=
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomIso A X.val Y.val
  exact SSet.uliftFunctor.{u + 1, u}.mapIso e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso X Y

def normalizedKProjectiveDerivedHomMap (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X.val)).obj Y.val) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
      ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)

open _root_.SSet.modelCategoryQuillen in
lemma normalizedKProjectiveDerivedHomMap_homotopyEquivalence (X Y : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveDerivedHomMap A X Y) := by
  have : KanComplex (SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X.val)).obj Y.val)) :=
    HomotopicalAlgebra.isFibrant_of_fibration (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A X Y).hom
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedKProjectiveHomIso A X Y)).comp
    (_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource_isFullyFaithful A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))

end SerrePositivity.ComplexLimits
