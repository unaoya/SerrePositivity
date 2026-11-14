module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneTrivialFibration
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopProperties
public import SerrePositivity.EInfinity.PowerOperation.TerminalKanHomotopy

/-!
# Γ と loop Γ の恒等 cone の全次数の一元性

DAG XIII §2.2 の Ω 比較への前段。同じ cone から零複体への零射の準同型性を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open scoped Simplicial
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- loop Γ も零複体を台の終対象に送る。 -/
def gammaLoopZeroIsTerminal :
    IsTerminal ((gammaLoopFunctor A).obj (HomologicalComplex.zero : Complex A)).right := by
  have := gammaLoopFunctor_preservesFiniteLimits A
  exact IsTerminal.isTerminalObj (gammaLoopFunctor A ⋙ PointedSimplicialSet.forget)
    (HomologicalComplex.zero : Complex A) HomologicalComplex.isZero_zero.isTerminal

lemma gammaIdentityCone_homotopy_subsingleton (M : Complex A) (n : ℕ)
    (x : ((gammaPointedFunctor A).obj (mappingCone (𝟙 M))).right _⦋0⦌) :
    Subsingleton (KanHomotopy
      ((gammaPointedFunctor A).obj (mappingCone (𝟙 M))).right n x) :=
  kanHomotopy_subsingleton_of_terminal_comparison _
    (gammaIdentityCone_zero_piIsomorphism A M) (gammaZeroIsTerminal A) n x

lemma gammaLoopIdentityCone_homotopy_subsingleton (M : Complex A) (n : ℕ)
    (x : ((gammaLoopFunctor A).obj (mappingCone (𝟙 M))).right _⦋0⦌) :
    Subsingleton (KanHomotopy
      ((gammaLoopFunctor A).obj (mappingCone (𝟙 M))).right n x) := by
  have := identityCone_zero_quasiIso A M
  exact kanHomotopy_subsingleton_of_terminal_comparison
    (((gammaLoopFunctor A).map
      (0 : mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A))).right)
    (gammaLoopMap_kanPiIsomorphism A _) (gammaLoopZeroIsTerminal A) n x

end SerrePositivity.EInfinity.PowerOperation
