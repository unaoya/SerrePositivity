module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedDoldKanComparison
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedOrdinaryDerivedHom

/-!
# 同じ半自由標的を通る実自由 Hom と D(R) Hom の接合 span

概要：同じ S(B.carrier) の正規化 Hom を中間項に、元の自由 Hom 共通項と D(R) Hom へ送る。
方針：元の標的 augmentation・同じ実 DK 同型・自由 Hom 弱比較を合成する。
規約：元の自由 probe・標的代数・通常導来源の値を保つ。
使われ方：元の標準自由単位比較の全族による検出。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

abbrev freeDerivedHomTestSpace (X : Complex A) (B : (operad A).Algebra) : SSet.{u + 1} :=
  SSet.uliftFunctor.{u + 1, u}.obj
    (((ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
      (ComplexLimits.complexSemifreeResolutionValue A B.carrier).val)

abbrev freeDerivedHomCommonSpace (X : Complex A) (B : (operad A).Algebra) : SSet.{u + 1} :=
  SSet.uliftFunctor.{u + 1, u}.obj (((freeNormalizedHomMiddle A).obj (Opposite.op X)).obj B)

abbrev freeDerivedHomStandardSpace (X : Complex A) (B : (operad A).Algebra) : SSet.{u + 1} :=
  SSet.uliftFunctor.{u + 1, u}.obj
    ((((freeProbeFunctor A).op ⋙ sourceFrameHom A).obj (Opposite.op X)).obj B)

def freeDerivedHomToCommonSmall (X : Complex A) (B : (operad A).Algebra) :
    (((ComplexLimits.normalizedProbeTensorHom A).obj (Opposite.op X)).obj
      (ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) ⟶
    (((freeNormalizedHomMiddle A).obj (Opposite.op X)).obj B) :=
  ComplexLimits.normalizedProbeTargetReplacementMap A X B.carrier ≫
    (ComplexLimits.normalizedProbeHomDoldKanIso A X B.carrier).hom ≫
      (((freeNormalizedHomFromDoldKan A).app (Opposite.op X)).app B)

def freeDerivedHomToCommon (X : Complex A) (B : (operad A).Algebra) :
    freeDerivedHomTestSpace A X B ⟶ freeDerivedHomCommonSpace A X B :=
  SSet.uliftFunctor.{u + 1, u}.map (freeDerivedHomToCommonSmall A X B)

def freeDerivedHomFromStandard (X : Complex A) (B : (operad A).Algebra) :
    freeDerivedHomStandardSpace A X B ⟶ freeDerivedHomCommonSpace A X B :=
  SSet.uliftFunctor.{u + 1, u}.map (((freeNormalizedHomFromStandard A).app (Opposite.op X)).app B)

def freeDerivedHomToUnderlying (X : Complex A) (B : (operad A).Algebra) :
    freeDerivedHomTestSpace A X B ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B.carrier)) :=
  ComplexLimits.normalizedOrdinaryDerivedHomMap A X B.carrier

end SerrePositivity.EInfinity.BarrattEccles
