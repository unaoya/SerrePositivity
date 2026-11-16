module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorTransport
public import SerrePositivity.EInfinity.SimplexCuts.Faces
public import SerrePositivity.EInfinity.SimplexCuts.NormalizedGenerators

/-!
# 元の切断の指定面から来る同じ生成元の族

Berger–Fresse §2.2.6、M14 L12a、報告 §354。
既存のcutTensorの入力族を短い記法で読み、元の全出力次数を計算する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じcutTensorの元の指定面による生成元の族の記法（BF §2.2.6）。 -/
def cutGeneratorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    Fin r → Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
  fun a => ⟨outputDegree s v a,
    gen A S (outputDegree s v a) (S.map (face s v a).op x)⟩

/-- 元の生成元の族の全次数は既存の出力次数の和（BF §2.2.3）。 -/
lemma vectorDegree_cutGeneratorFamily (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    vectorDegree (chains A S) r (cutGeneratorFamily A S s v x) = m + q + 1 - r := by
  change degreeSum r (outputDegree s v) = _
  rw [degreeSum_eq_sum, outputDegree_sum]

end SerrePositivity.EInfinity.SimplexCuts
