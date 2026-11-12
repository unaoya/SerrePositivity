module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorOrbitComplex
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# 固定 arity の色の個数と二色の arity

HA 3.2.4.7 の自由比較で、固定 arity の標準代表の添字を左右の入力数へ移す。
標準代表の安定化群を、係数比較が使う実際の二色部分群に同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory

/-- 左右の入力数を足した arity では、個数による代表は元の標準パターンである。 -/
lemma binaryTensorCountPattern_add (m n : ℕ) :
    binaryTensorCountPattern (m + n) ⟨m, by omega⟩ = binaryTensorStandardPattern m n := by
  unfold binaryTensorCountPattern
  apply eq_of_heq
  have he {k l : ℕ} (h : k = l) :
      HEq (binaryTensorStandardPattern m k) (binaryTensorStandardPattern m l) := by
    subst l
    rfl
  exact (cast_heq _ _).trans (he (by change m + n - m = n; omega))

/-- 指定代表の安定化群は、係数比較が使う指定二色部分群に等しい。 -/
lemma binaryTensorPatternSubgroup_add (m n : ℕ) :
    binaryTensorPatternSubgroup (m + n) (ULift.up ⟨m, by omega⟩) =
      (BarrattEccles.twoColorPermutationHom.{u} m n).range := by
  ext g
  change g.down • binaryTensorCountPattern (m + n) ⟨m, by omega⟩ =
      binaryTensorCountPattern (m + n) ⟨m, by omega⟩ ↔ _
  rw [binaryTensorCountPattern_add]
  exact (binaryTensorStandard_mem_twoColor_iff m n g.down).symm

/-- 群の同定は、周囲の対称群への包含を変えない。 -/
def binaryTensorPatternGroupEquiv (m n : ℕ) :
    binaryTensorPatternSubgroup (m + n) (ULift.up ⟨m, by omega⟩) ≃*
      (BarrattEccles.twoColorPermutationHom.{u} m n).range :=
  MulEquiv.subgroupCongr (binaryTensorPatternSubgroup_add m n)

/-- 同定後の群の元も、元の対称群の同じ置換である。 -/
lemma binaryTensorPatternGroupEquiv_val (m n : ℕ)
    (g : binaryTensorPatternSubgroup (m + n) (ULift.up ⟨m, by omega⟩)) :
    (binaryTensorPatternGroupEquiv m n g).val = g.val := rfl

/-- 固定 arity と左入力数の組を、左右の入力数の組へ再添字する。 -/
def binaryTensorCountIndexEquiv : (Σ r : ℕ, ULift.{u} (Fin (r + 1))) ≃ ℕ × ℕ :=
  (Equiv.sigmaCongrRight (fun r => Equiv.ulift.trans
    (Finset.Nat.antidiagonalEquivFin r).symm)).trans
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd

end SerrePositivity.EInfinity
