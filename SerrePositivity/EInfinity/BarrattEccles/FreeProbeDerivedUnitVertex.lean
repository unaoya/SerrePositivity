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
open SerrePositivity.InfinityCategories DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeVertex (x : (derivedInfinityCategory A) _⦋0⦌) : (CAlg_R A) _⦋0⦌ :=
  cAlgVertex A ((freeProbeFunctor A).obj (derivedInfinityCategoryVertexEquiv A x).val)

def derivedFreeProbeSourceIso (x : (derivedInfinityCategory A) _⦋0⦌) :
    VertexIso ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (derivedInfinityCategoryVertexEquiv A x).val)) x :=
  ComplexLimits.complexOrdinaryDerivedSource_semifreeVertexIso A
    (derivedInfinityCategoryVertexEquiv A x) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        ((derivedInfinityCategoryVertexEquiv A).symm_apply_apply x))

def freeProbeDerivedUnitComponent (X : Complex A) :
    (HomotopyCategory.mk ((ComplexLimits.complexOrdinaryDerivedSource A).app
      (Opposite.op ⦋0⦌) (nerveVertex X)) : hoFunctor.obj (derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
        (cAlgVertex A ((freeProbeFunctor A).obj X))) :=
  functorHomEvaluate (freeProbeDerivedUnit A) (nerveVertex X) ≫
    (VertexIso.map (freeProbeCAlgSource_vertexIso A X) (cAlgForgetDerived A)).hom

def derivedFreeProbeUnitHom (x : (derivedInfinityCategory A) _⦋0⦌) :
    (HomotopyCategory.mk x : hoFunctor.obj (derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
        (derivedFreeProbeVertex A x)) :=
  (derivedFreeProbeSourceIso A x).inv ≫
    freeProbeDerivedUnitComponent A (derivedInfinityCategoryVertexEquiv A x).val

def derivedFreeProbeUnitEdge (x : (derivedInfinityCategory A) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj (derivedInfinityCategory A)) x
      ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) (derivedFreeProbeVertex A x)) :=
  Classical.choose (homotopyCategory_homMk_surjective x _ (derivedFreeProbeUnitHom A x))

lemma derivedFreeProbeUnitEdge_homMk (x : (derivedInfinityCategory A) _⦋0⦌) :
    Truncated.HomotopyCategory.homMk (derivedFreeProbeUnitEdge A x) =
      derivedFreeProbeUnitHom A x :=
  Classical.choose_spec (homotopyCategory_homMk_surjective x _ (derivedFreeProbeUnitHom A x))

end SerrePositivity.EInfinity.BarrattEccles
