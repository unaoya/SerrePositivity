module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitDiagonal

/-!
# 同じ orbit 全複体の各次数を有限な余積へ移す

DAG XIII Construction 2.2.6 の鎖模型比較の補助。
零成分を除いた同じ余積と、元の直和全複体の項を指定同型で比べる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]
variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)

/-- 支持する成分の指定余積から、元の直和全複体の同じ項への同型。 -/
def cyclicOrbitTotalDegreeSupportIso :
    (∐ fun q : {q : CyclicOrbitDiagonal n // q.1.2 ≤ 0 ∧ q.1.1 ≤ d} =>
      cyclicOrbitDiagonalSummand p k M n q.1) ≅
      ((cyclicOrbitTotalFunctor p k).obj M).X n := by
  classical
  exact coproductZeroSupportIso (cyclicOrbitDiagonalSummand p k M n)
    (fun q => q.1.2 ≤ 0 ∧ q.1.1 ≤ d)
    (cyclicOrbitDiagonalSummand_isZero p k M d n)

/-- 元の直和全複体の項を、同じ有限区間に添字付けた余積へ移す。 -/
def cyclicOrbitTotalDegreeFiniteSumIso :
    ((cyclicOrbitTotalFunctor p k).obj M).X n ≅
      ∐ fun s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)} =>
        cyclicOrbitDiagonalSummand p k M n
          ((cyclicOrbitFiniteDiagonalEquiv d n).symm s).1 :=
  (cyclicOrbitTotalDegreeSupportIso p k M d n).symm ≪≫
    (Sigma.reindex (cyclicOrbitFiniteDiagonalEquiv d n).symm
      (fun q => cyclicOrbitDiagonalSummand p k M n q.1)).symm

end SerrePositivity.EInfinity.PowerOperation
