module

public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTotalQuotientPerfectZero

/-!
概要：固定 dg 提示源の全対象商の実 ν 値が零圏であることを認証する。
方針：D-20 の全対象商 Perf 零性を、元の presented Perf 評価同値で輸送する。
規約：元の零角と固定 ν を保ち、K-B の特殊な核の証明を import・複製しない。
使われ方：Sp-6 の実零化四角形・相対 Verdier 提示の零角入力を供給する。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R]

lemma dgFixedNullInput_isZeroCategory (A : PerfDGInput.{u, v} R) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R A)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTotalQuotientPerfect_isZero_of_equivalence R A
    (dgKInputStableValue R (dgFixedNullInput R A))
    (presentedPerfectDGQCatEvaluationEquivalence R (dgFixedNullInput R A))

end SerrePositivity.KST.LocalizingInvariants
