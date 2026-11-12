module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneConeFibration
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneFiniteLimits
public import SerrePositivity.EInfinity.PowerOperation.ShortExactPullbackZero
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Γ の cone の指定 strict fiber

DAG XIII §2.2 の Ω 比較への前段。実際の回転 cone 短完全列と零複体を使い、
有限極限保存によって同じ四射を Γ の strict 引き戻しへ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 元の回転 cone の短複体は、既存の次数別 splitting により短完全。 -/
lemma coneRotateShortComplex_shortExact {M N : Complex A} (f : M ⟶ N) :
    (mappingCone.triangleRotateShortComplex f).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (mappingCone.triangleRotateShortComplexSplitting f n).shortExact

/-- 零複体の Γ は、同じ有限極限保存により終対象である。 -/
def gammaZeroIsTerminal :
    IsTerminal ((truncatedDoldKanFunctor A).obj (HomologicalComplex.zero : Complex A)) := by
  have := gammaFunctor_preservesFiniteLimits A
  exact IsTerminal.isTerminalObj (truncatedDoldKanFunctor A)
    (HomologicalComplex.zero : Complex A) HomologicalComplex.isZero_zero.isTerminal

/-- 零複体の Γ と通常の一点の標準同型。 -/
def gammaZeroIso :
    (truncatedDoldKanFunctor A).obj (HomologicalComplex.zero : Complex A) ≅ 𝟙_ SSet.{u} :=
  (gammaZeroIsTerminal A).uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

/-- 指定 cone の strict fiber は、元の Γ の四射からなる引き戻しである。 -/
lemma gammaCone_isPullback {M N : Complex A} (f : M ⟶ N) :
    IsPullback ((truncatedDoldKanFunctor A).map (mappingCone.inr f))
      ((truncatedDoldKanFunctor A).map (0 : N ⟶ (HomologicalComplex.zero : Complex A)))
      ((truncatedDoldKanFunctor A).map (mappingCone.triangle f).mor₃)
      ((truncatedDoldKanFunctor A).map
        (0 : (HomologicalComplex.zero : Complex A) ⟶ M⟦(1 : ℤ)⟧)) := by
  have := gammaFunctor_preservesFiniteLimits A
  have h := shortExact_isPullback_zero (coneRotateShortComplex_shortExact A f)
    (HomologicalComplex.zero : Complex A) HomologicalComplex.isZero_zero
  exact (truncatedDoldKanFunctor A).map_isPullback h

end SerrePositivity.EInfinity.PowerOperation
