module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnit

/-!
# 元の D(R) の任意頂点の実自由 probe への単位辺

概要：元の任意 D(R) 頂点から同じ自由 probe の U 像への実辺を構成する。
方針：元の半自由頂点表示と全源の導来単位を評価し、同じ射の類の辺を取る。
規約：選んだ辺の homMk は元の単位の射そのもの。
使われ方：U の comma fiber の始対象候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeVertex (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) : (CAlg_R A) _⦋0⦌ :=
  cAlgVertex A ((freeProbeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x).val)

def derivedFreeProbeSourceIso (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x).val)) x :=
  _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_semifreeVertexIso A
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A).symm_apply_apply x))

def freeProbeDerivedUnitComponent (X : Complex A) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
        (cAlgVertex A ((freeProbeFunctor A).obj X))) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeDerivedUnit A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (freeProbeCAlgSource_vertexIso A X) (cAlgForgetDerived A)).hom

def derivedFreeProbeUnitHom (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    (HomotopyCategory.mk x : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
        (derivedFreeProbeVertex A x)) :=
  (derivedFreeProbeSourceIso A x).inv ≫
    freeProbeDerivedUnitComponent A (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv A x).val

def derivedFreeProbeUnitEdge (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) x
      ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) (derivedFreeProbeVertex A x)) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x _ (derivedFreeProbeUnitHom A x))

lemma derivedFreeProbeUnitEdge_homMk (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    Truncated.HomotopyCategory.homMk (derivedFreeProbeUnitEdge A x) =
      derivedFreeProbeUnitHom A x :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x _ (derivedFreeProbeUnitHom A x))

end SerrePositivity.EInfinity.BarrattEccles
