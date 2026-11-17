module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementDerivedRoofComparison
public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveElementRoofWeak
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomLiftIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PinchedEndpointFamilyArrow

/-!
# 元の通常導来屋根の全制限を同じ端点へ戻す弱な基準族

DAG XIII §2.2 の native な降下の補助。既存の同じ K-projective 屋根族を使い、
全添字と二脚を保持して比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof
open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories (intervalFamilyHom intervalFamilyHom_precomp
  intervalFamilyHomPrecomp)
open TheSliceAndJoinConstructions (nerveVertex)
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma complexRelativeDerivedSource_vertex :
    (complexRelativeDerivedSource A).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ ((complexRelativeUp A).obj X)) =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) :=
  congrArg ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌))
    (ComposableArrows.ext₀ rfl)

def complexRelativeElementReferencePinchedMap :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (normalizedTensorElementIndex A X Y) ≫
    normalizedTensorElementOrdinaryPinchedMap A X Y) ≫
      (pinchedEndpointIso (complexRelativeDerivedSource_vertex A X).symm
        (complexRelativeDerivedSource_vertex A Y).symm).hom

lemma complexRelativeElementReferencePinchedMap_roof_arrow :
    let I := normalizedTensorElementIndex A X Y
    let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down I)).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk (intervalFamilyHom (complexRelativeElementReferencePinchedMap A X Y ≫
      MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
      Arrow.mk (T.map (normalizedTensorElementDerivedRoof A X Y)) := by
  let I := normalizedTensorElementIndex A X Y
  let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down I)).app
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
  have hn := (congrArg Arrow.mk (normalizedTensorElementOrdinaryPinchedMap_family A X Y)).trans
    (normalizedTensorElementDerivedRoofFamily_arrow A X Y)
  have hp := congrArg T.mapArrow.obj hn
  have he := pinchedEndpointFamily_arrow (complexRelativeDerivedSource_vertex A X).symm
    (complexRelativeDerivedSource_vertex A Y).symm
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down I ≫ normalizedTensorElementOrdinaryPinchedMap A X Y)
  refine he.trans ?_
  simpa only [T, I, Functor.mapArrow_obj, Arrow.mk_hom, nerveVertex, Category.assoc,
    intervalFamilyHom_precomp, intervalFamilyHomPrecomp] using hp

lemma complexRelativeElementReferencePinchedMap_weak (X Y : KProjectiveComplex A) :
    IsWeakHomotopyEquivalence (complexRelativeElementReferencePinchedMap A X.val Y.val) := by
  have hi := (MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homLiftIso (normalizedTensorElementIndex A X.val Y.val))).isWeakHomotopyEquivalence
  have hp := normalizedTensorElementOrdinaryPinchedMap_weak A X Y
  have he := (MorphismSpaces.isPrecompositionEquivalence_of_iso
    (pinchedEndpointIso (complexRelativeDerivedSource_vertex A X.val).symm
      (complexRelativeDerivedSource_vertex A Y.val).symm)).isWeakHomotopyEquivalence
  exact (hi.comp hp).comp he

end SerrePositivity.EInfinity.PowerOperation
