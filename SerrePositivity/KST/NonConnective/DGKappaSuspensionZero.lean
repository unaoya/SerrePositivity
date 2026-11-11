module
public import SerrePositivity.KST.NonConnective.DGKInputDerivedZero
public import SerrePositivity.KST.NonConnective.DGKappaSuspension
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness

/-!
概要：固定 ν が零なら、同じ実 cone の全対象は perfect で、元の実懸垂の固定 ν も零。
方針：元の主導来零性と実商の指定 ε による全加群の acyclic 性を使う。
規約：別の零商に置き換えず、元の cell 分解と実商を保持する。
使われ方：K-7 f の零保存を同じ全反復へ伝える。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R A κ)
  (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R A))
include hA

/-- 固定 ν が零の元の cone では、全対象が同じ perfect 零化集合に属する。 -/
theorem dgKappaConePerfectObjects_all (M : DGKappaCone R A I) :
    M ∈ dgKappaConePerfectObjects R A I :=
  (modulePerfect R A).prop_of_isZero (dgKInputDerived_isZero R A hA _)

/-- 同じ実懸垂上の全加群は、各対象の元の指定 ε により acyclic。 -/
theorem dgKappaSuspensionModule_acyclic (M : RightModule R (dgKappaSuspensionKInput R A I)) :
    moduleAcyclic R (dgKappaSuspensionKInput R A I)
      (ForgetEnrichment.of (Complex R) M) := by
  intro x
  exact DGQuotient.quotientModule_value_acyclic R _ _ M ⟨x.val,
    dgKappaConePerfectObjects_all R A I hA _⟩

/-- 同じ元の実懸垂の固定 ν は、元入力の固定 ν の零性を保つ。 -/
theorem dgKappaSuspensionStableValue_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgKappaSuspensionKInput R A I)) := by
  apply dgKInputStableValue_isZero_of_derived R (dgKappaSuspensionKInput R A I)
  intro X
  obtain ⟨⟨N⟩⟩ := X
  exact moduleToDerived_isZero_of_acyclic R _
    (dgKappaSuspensionModule_acyclic R A I hA (ForgetEnrichment.to (Complex R) N))

end SerrePositivity.KST.NonConnective
