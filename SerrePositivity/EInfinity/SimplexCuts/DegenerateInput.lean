module

public import SerrePositivity.EInfinity.SimplexCuts.RawAction
public import SerrePositivity.EInfinity.SimplexCuts.CollapsedFace

/-!
# 退化入力に対する一般の切断和の消滅

Berger–Fresse §2.2.6。一つの入力退化が潰す隣接頂点を同じ色の面に集め、
その正規化生成元が零となることを用いる（5a-5a L07）。
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

/-- L07 の証明の分割：和を取る前に、各切断項の一因子が退化する。 -/
lemma cutTensor_degenerate {m q r : ℕ} (S : SSet.{0}) (s : Cut m (q + 1))
    (u : Surjection.Word r (m + 1)) (i : Fin (q + 1)) (x : S _⦋q⦌) :
    cutTensor A S s u (S.σ i x) = 0 := by
  obtain ⟨a, ha⟩ := face_comp_sigma_not_mono s u i
  apply tensorValue_eq_zero (chains A S) r (outputDegree s u) _ a
  have hx : S.map (face s u a).op (S.σ i x) =
      S.map (face s u a ≫ SimplexCategory.σ i).op x := by
    exact (ConcreteCategory.congr_hom (S.map_comp (SimplexCategory.σ i).op (face s u a).op) x).symm
  rw [hx]
  exact gen_map_of_not_mono A S (outputDegree s u a) _ ha x

/-- 退化入力に対する実 BF 切断和の消滅（BF §2.2.6）。 -/
lemma cutSum_degenerate (S : SSet.{0}) {r d q : ℕ}
    (u : Surjection.BasisWord (r + 1) d) (i : Fin (q + 1)) (x : S _⦋q⦌) :
    cutSum A S u (S.σ i x) = 0 := by
  unfold cutSum
  have h : ∑ s : Cut (r + d) (q + 1),
      cutTerm A S s (positiveWord u) (S.σ i x) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    unfold cutTerm cutTensorAt
    rw [cutTensor_degenerate A S s (positiveWord u) i x, map_zero, smul_zero]
  rw [h, map_zero]

end SerrePositivity.EInfinity.SimplexCuts
