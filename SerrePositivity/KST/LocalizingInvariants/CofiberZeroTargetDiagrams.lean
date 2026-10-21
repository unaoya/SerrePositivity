module

public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactDiagrams
public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationComparisonProjection
public import SerrePositivity.InfinityCategories.Stable.CofiberZeroSource

/-!
概要：零終点矢印の元の cofiber 全族を、同じ始点の suspension 全図式と比較する。
方針：元の二つの零角を保持して suspension 図式圏へ入れ、始点評価の fiber で比較する。
規約：比較は始点で恒等。使われ方：一般商の suspension 比較の二次の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsZeroTargetArrow (a.app (Opposite.op ⦋0⦌) x))

include ha in
lemma squareAt_isSuspension (x : A _⦋0⦌) :
    IsSuspensionDiagramVertex ((squares X a).app (Opposite.op ⦋0⦌) x) := by
  refine ⟨squareAt_zero X a x, ?_, squareAt_isPushout X a x⟩
  let s := cofiberSquareAt X a x
  change IsZeroVertex (squareVertex s.square 1 0)
  rw [s.target_vertex]
  have ht := (intervalFunctorVertexTypedEdge (a.app (Opposite.op ⦋0⦌) x)).tgt_eq
  change X.δ 0 (intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x)) = _ at ht
  change IsZeroVertex (X.δ 0 (intervalFunctorVertexEdge (a.app (Opposite.op ⦋0⦌) x)))
  rw [ht]
  exact ha x

def zeroTargetDiagrams : A ⟶ suspensionDiagrams X :=
  fullSubcomplexLift IsSuspensionDiagramVertex (squares X a) (squareAt_isSuspension X a ha)

lemma zeroTargetDiagrams_source :
    zeroTargetDiagrams X a ha ≫ suspensionDiagramEvaluation X 0 0 =
      a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have he := congrArg (fun f => f ≫ evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (squares_bottom X a)
  rw [Category.assoc, stable_pre_evaluateFunctorAt] at he
  rw [suspensionDiagramEvaluation, ← Category.assoc,
    zeroTargetDiagrams, fullSubcomplexLift_ι]
  exact he

lemma zeroTargetDiagrams_target :
    zeroTargetDiagrams X a ha ≫ suspensionDiagramEvaluation X 1 1 = cofiber X a := by
  rw [suspensionDiagramEvaluation, ← Category.assoc,
    zeroTargetDiagrams, fullSubcomplexLift_ι]
  rfl

def suspensionDiagramsAtSource : A ⟶ suspensionDiagrams X :=
  (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
    SuspensionExact.diagrams X

lemma suspensionDiagramsAtSource_source :
    suspensionDiagramsAtSource X a ≫ suspensionDiagramEvaluation X 0 0 =
      a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [suspensionDiagramsAtSource, Category.assoc, SuspensionExact.diagrams_source,
    Category.comp_id]

lemma zeroTargetDiagrams_sameSource :
    zeroTargetDiagrams X a ha ≫ suspensionDiagramEvaluation X 0 0 =
      suspensionDiagramsAtSource X a ≫ suspensionDiagramEvaluation X 0 0 := by
  rw [zeroTargetDiagrams_source, suspensionDiagramsAtSource_source]

def zeroTargetDiagramComparison : FunctorIso (zeroTargetDiagrams X a ha)
    (suspensionDiagramsAtSource X a) :=
  suspensionDiagramFamilyIso _ _ (zeroTargetDiagrams_sameSource X a ha)

lemma zeroTargetDiagramComparison_source_arrow :
    Arrow.mk (FunctorIso.postcomp (zeroTargetDiagramComparison X a ha)
      (suspensionDiagramEvaluation X 0 0)).hom =
        Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
          (suspensionDiagramsAtSource X a ≫ suspensionDiagramEvaluation X 0 0)) :
            hoFunctor.obj ((ihom A).obj X))) :=
  functorIsoOfTrivialKanFibration_projection_arrow _ _ _ (zeroTargetDiagrams_sameSource X a ha)

def zeroTargetRelativeIso : FunctorIso (cofiber X a)
    ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      SuspensionExact.map X) := by
  have e := FunctorIso.postcomp (zeroTargetDiagramComparison X a ha)
    (suspensionDiagramEvaluation X 1 1)
  rw [zeroTargetDiagrams_target] at e
  simpa only [suspensionDiagramsAtSource, Category.assoc,
    SuspensionExact.diagrams_target] using e

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
