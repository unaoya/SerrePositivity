module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryIndex
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryFaces

/-!
# 出力の一面を削除した切断の境界項

Berger–Fresse §2.2.6–7、M14 L09a。
色を一つ指定してその面を削除し、同じ全次数へ移送する。
次数零の色は零とし、他の色の面とBF符号は保持する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 指定色の一面を削除した、同じ正規化生成元のテンソル（BF §2.2.6）。 -/
def deletedCutTensor {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s u a)
    (j : Fin (outputDegree s u a + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).X (-((m + q + 1 - r : ℕ) : ℤ) + 1) := by
  let d := outputDegree s u
  let e := Function.update d a (d a - 1)
  let v : ∀ b, (chains A S).X (-(e b : ℤ)) := fun b => by
    by_cases h : b = a
    · subst b
      simpa only [e, Function.update_self] using
        gen A S (d a - 1) (S.map (boundaryFace (d a) ha j ≫ face s u a).op x)
    · have he : e b = d b := Function.update_of_ne h _ _
      exact (eqToHom (congrArg (fun t : ℤ => (chains A S).X t)
        (congrArg (fun k : ℕ => -(k : ℤ)) he.symm))).hom
          (gen A S (d b) (S.map (face s u b).op x))
  have h₁ : degreeSum r e + 1 = degreeSum r d := degreeSum_delete d a ha
  have h₂ : degreeSum r d = m + q + 1 - r :=
    (degreeSum_eq_sum r d).trans (outputDegree_sum s u)
  have h : -(degreeSum r e : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1 := by omega
  exact (eqToHom (congrArg (fun t : ℤ => (power (chains A S) r).X t) h)).hom
    (tensorValue (chains A S) r e v)

/-- 出力テンソルの微分のKoszul符号と、面の交代符号の和（BF §2.2.7）。 -/
def outputBoundarySign {m q r : ℕ} (s : Cut m q) (u : Surjection.Word r (m + 1))
    (a : Fin r) (j : Fin (outputDegree s u a + 1)) : ℤ :=
  cutSign s u.val * (-1)^((∑ b ∈ Finset.univ.filter (fun b : Fin r => b < a),
    outputDegree s u b) + j.val)

/-- 一つの出力面の符号付き境界値。零次の境界も同じ添字で零として残す。 -/
def outputBoundaryTerm {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r)
    (j : Fin (outputDegree s u a + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).X (-((m + q + 1 - r : ℕ) : ℤ) + 1) :=
  if ha : 0 < outputDegree s u a then
    outputBoundarySign s u a j • deletedCutTensor A S s u a ha j x
  else 0

end SerrePositivity.EInfinity.SimplexCuts
