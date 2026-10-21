module

public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.Stable.SuspensionEquivalence
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability

/-!
概要：選んだ完全 suspension の全族を実 suspension 図式へ入れ、標準自己同値と比較する。
方針：普遍 cofiber 族の底辺を零終点矢印に制限し、始点評価上の選択を比較する。
規約：同じ全単体上の map を保つ。使われ方：一般商 Q の shift と逆 shift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

def squares : X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  arrow X ≫ CofiberFamily.squares X (𝟙 _)

lemma squares_bottom : squares X ≫ (pre squareBottomEdge).app X = arrow X := by
  rw [squares, Category.assoc, CofiberFamily.squares_bottom, Category.comp_id]

lemma squares_corner (x : X _⦋0⦌) (i j : Fin 2) :
    (squares X ≫ evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌) x =
      squareVertex (squareDiagram ((squares X).app (Opposite.op ⦋0⦌) x)) i j := by
  have hs : functorVertex (squareDiagram ((squares X).app (Opposite.op ⦋0⦌) x)) =
      (squares X).app (Opposite.op ⦋0⦌) x := (functorVertexEquiv _ _).apply_symm_apply _
  change (evaluateFunctorAt _).app _ ((squares X).app _ x) = _
  rw [← hs, evaluateFunctorAt_functorVertex]
  rfl

lemma squares_isSuspension (x : X _⦋0⦌) :
    IsSuspensionDiagramVertex ((squares X).app (Opposite.op ⦋0⦌) x) := by
  have h := congrArg (fun f => f ≫ evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (squares_bottom X)
  rw [Category.assoc, stable_pre_evaluateFunctorAt] at h
  have hv : squareBottomEdge.{u}.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  rw [hv] at h
  have hz := arrow_zero_target X x
  change IsZeroVertex ((arrow X ≫ evaluateFunctorAt _).app (Opposite.op ⦋0⦌) x) at hz
  rw [← h, squares_corner] at hz
  exact ⟨CofiberFamily.squareAt_zero X (𝟙 _) ((arrow X).app _ x), hz,
    CofiberFamily.squareAt_isPushout X (𝟙 _) ((arrow X).app _ x)⟩

def diagrams : X ⟶ suspensionDiagrams X :=
  fullSubcomplexLift IsSuspensionDiagramVertex (squares X) (squares_isSuspension X)

lemma diagrams_source : diagrams X ≫ suspensionDiagramEvaluation X 0 0 = 𝟙 X := by
  have h := congrArg (fun f => f ≫ evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (squares_bottom X)
  rw [Category.assoc, stable_pre_evaluateFunctorAt, arrow_source] at h
  rw [suspensionDiagramEvaluation, ← Category.assoc, diagrams, fullSubcomplexLift_ι]
  exact h

lemma diagrams_target : diagrams X ≫ suspensionDiagramEvaluation X 1 1 = map X := by
  rw [suspensionDiagramEvaluation, ← Category.assoc, diagrams, fullSubcomplexLift_ι]
  rfl

def canonicalIso : FunctorIso (map X) (suspensionQCatEquivalence X).hom := by
  have e := FunctorIso.postcomp
    (suspensionDiagramFamilyIso (diagrams X) (suspensionDiagramSourceEquivalence X).inv
      (by rw [diagrams_source, suspensionDiagramSourceEquivalence_inv_source]))
    (suspensionDiagramEvaluation X 1 1)
  rw [diagrams_target, ← suspensionQCatEquivalence_hom] at e
  exact e

def equivalence : QCatEquivalence X X where
  hom := map X
  inv := (suspensionQCatEquivalence X).inv
  homInvIso := (FunctorIso.postcomp (canonicalIso X) (suspensionQCatEquivalence X).inv) ≪≫
    (suspensionQCatEquivalence X).homInvIso
  invHomIso := (FunctorIso.precomp (canonicalIso X) (suspensionQCatEquivalence X).inv) ≪≫
    (suspensionQCatEquivalence X).invHomIso

def inverseExactMap (A : StableCategory.{u}) : ExactMap A A :=
  ⟨(equivalence A.obj).inv,
    isExactFunctor_of_isQCatEquivalence (equivalence A.obj).symm.isQCatEquivalence⟩

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
