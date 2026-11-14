module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

def squares : X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares X (𝟙 _)

lemma squares_bottom : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares_bottom, Category.comp_id]

lemma squares_corner (x : X _⦋0⦌) (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X).app (Opposite.op ⦋0⦌) x)) i j := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X).app (Opposite.op ⦋0⦌) x)) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X).app (Opposite.op ⦋0⦌) x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app _ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X).app _ x) = _
  rw [← hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  rfl

lemma squares_isSuspension (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X).app (Opposite.op ⦋0⦌) x) := by
  have h := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_bottom X)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge.{u}.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  rw [hv] at h
  have hz := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow_zero_target X x
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _).app (Opposite.op ⦋0⦌) x) at hz
  rw [← h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_corner] at hz
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squareAt_zero X (𝟙 _) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X).app _ x), hz,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squareAt_isPushout X (𝟙 _) ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X).app _ x)⟩

def diagrams : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_isSuspension X)

lemma diagrams_source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 = 𝟙 X := by
  have h := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_bottom X)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow_source] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact h

lemma diagrams_target : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  rfl

def canonicalIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).hom := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramFamilyIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv
      (by rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence_inv_source]))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams_target, ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence_hom] at e
  exact e

def equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X X where
  hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X
  inv := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).inv
  homInvIso := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).inv) ≪≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).homInvIso
  invHomIso := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).inv) ≪≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).invHomIso

def inverseExactMap (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A A :=
  ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence A.obj).inv,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence A.obj).symm.isQCatEquivalence⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.canonicalIso := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.diagrams := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.diagrams_source := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.diagrams_target := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams_target

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.equivalence := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.inverseExactMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.inverseExactMap := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.inverseExactMap

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.squares := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.squares_bottom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.squares_corner := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_corner

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.squares_isSuspension := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares_isSuspension

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.canonicalIso._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.canonicalIso._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.canonicalIso._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.canonicalIso._proof_4 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.canonicalIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.diagrams.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.inverseExactMap._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.inverseExactMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SuspensionExact.squares.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.squares.eq_1
