module

public import SerrePositivity.EInfinity.SimplexCuts.CutTensor
public import SerrePositivity.EInfinity.SimplexCuts.Signs

/-!
# 一つの共通次数に値を持つ符号付き切断項

Berger–Fresse §2.2.6。出力次数の等式を明示した移送で、切断の和を取れる値域を作る。
退化した切断も同じ値域で零として保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 各切断のテンソルを、語長と入力次数で決まる共通成分へ送る（BF §2.2.6）。 -/
def cutTensorAt {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).X (-((m + q + 1 - r : ℕ) : ℤ)) :=
  (eqToHom (congrArg (fun t : ℤ => (power (chains A S) r).X t)
    (congrArg (fun t : ℕ => -(t : ℤ))
      ((degreeSum_eq_sum r (outputDegree s u)).trans (outputDegree_sum s u))))).hom
        (cutTensor A S s u x)

/-- 同じ BF 符号を掛けた切断項（BF §2.2.6）。 -/
def cutTerm {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).X (-((m + q + 1 - r : ℕ) : ℤ)) :=
  cutSign s u.val • cutTensorAt A S s u x

/-- L04 の移送後の帰結。退化した項は同じ和の値域で零。 -/
lemma cutTerm_eq_zero {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (h : ¬Nondegenerate s u.val) (x : S _⦋q⦌) :
    cutTerm A S s u x = 0 := by
  unfold cutTerm cutTensorAt
  rw [cutTensor_eq_zero A S s u h x, map_zero, smul_zero]

end SerrePositivity.EInfinity.SimplexCuts
