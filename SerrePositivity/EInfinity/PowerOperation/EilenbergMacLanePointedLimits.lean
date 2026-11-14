module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneFiniteLimits
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaWeakEquivalence
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Γ の零基点を保持した有限極限

DAG XIII §2.2 の Ω 比較への前段。基点を忘れる関手が極限を反映することにより、
同じ Γ の有限極限を零基点付きで保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

instance gammaPointedKan (M : Complex A) : SSet.KanComplex (gammaPointed A M).right :=
  gammaUnderlyingKan A M

/-- 同じ Γ の全関手の対象という表示でも、同じ Kan 性を読む。 -/
instance gammaPointedFunctorObjKan (M : Complex A) :
    SSet.KanComplex ((gammaPointedFunctor A).obj M).right := gammaUnderlyingKan A M

/-- 基点の零元も含めた同じ Γ の全関手は有限極限を保つ。 -/
lemma gammaPointedFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (gammaPointedFunctor A) := by
  have : PreservesFiniteLimits (gammaPointedFunctor A ⋙ PointedSimplicialSet.forget) := by
    change PreservesFiniteLimits (truncatedDoldKanFunctor A)
    exact gammaFunctor_preservesFiniteLimits A
  exact preservesFiniteLimits_of_reflects_of_preserves
    (gammaPointedFunctor A) PointedSimplicialSet.forget

/-- 零射は、同じ零基点を経由する零射に写る。 -/
lemma gammaPointedFunctor_preservesZeroMorphisms :
    (gammaPointedFunctor A).PreservesZeroMorphisms := by
  have := gammaPointedFunctor_preservesFiniteLimits A
  infer_instance

end SerrePositivity.EInfinity.PowerOperation
