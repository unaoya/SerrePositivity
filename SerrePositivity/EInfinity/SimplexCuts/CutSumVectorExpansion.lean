module

public import SerrePositivity.EInfinity.SimplexCuts.CutTensorDegreeTransport
public import SerrePositivity.EInfinity.SimplexCuts.RawAction

/-!
# 元の切断和の同じ斉次ベクトルによる展開

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §299。
同じ生成元と斉次テンソルを、元の等式移送と同じ複体射で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元の全切断和を同じ出力族の斉次テンソルで読む（BF §2.2.6）。 -/
lemma cutSum_eq_sum_vectorTensorAt (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    cutSum A S u x = ∑ s : Cut (r + d) q, cutSign s (positiveWord u).val •
      vectorTensorAt (chains A S) (r + 1)
        (fun a => ⟨outputDegree s (positiveWord u) a,
          gen A S (outputDegree s (positiveWord u) a) (S.map (face s (positiveWord u) a).op x)⟩)
        (-((d + q : ℕ) : ℤ))
        (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]; congr 1; congr 1; omega) := by
  unfold cutSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold cutTerm
  rw [map_zsmul]
  congr 1
  apply eq_of_heq
  exact (module_eqToHom_apply_heq _ _ _ _).trans
    ((cutTensorAt_heq_vectorTensor A S s (positiveWord u) x).trans
      (vectorTensorAt_heq (chains A S) (r + 1) _ _ _).symm)

end SerrePositivity.EInfinity.SimplexCuts
