module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.RawAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CollapsedFace

/-!
模型。文献の定義との比較は後で
# 退化入力に対する一般の切断和の消滅

Berger–Fresse §2.2.6。一つの入力退化が潰す隣接頂点を同じ色の面に集め、
その正規化生成元が零となることを用いる（5a-5a L07）。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- L07 の証明の分割：和を取る前に、各切断項の一因子が退化する。 -/
lemma cutTensor_degenerate {m q r : ℕ} (S : SSet.{0}) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1))
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (i : Fin (q + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s u (S.σ i x) = 0 := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face_comp_sigma_not_mono s u i
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_eq_zero (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u) _ a
  have hx : S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a).op (S.σ i x) =
      S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a ≫ SimplexCategory.σ i).op x := by
    exact (ConcreteCategory.congr_hom (S.map_comp (SimplexCategory.σ i).op (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a).op) x).symm
  rw [hx]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_map_of_not_mono A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a) _ ha x

/-- 退化入力に対する実 BF 切断和の消滅（BF §2.2.6）。 -/
lemma cutSum_degenerate (S : SSet.{0}) {r d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (i : Fin (q + 1)) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S u (S.σ i x) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum
  have h : ∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) (q + 1),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) (S.σ i x) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensorAt
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor_degenerate A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) i x, map_zero, smul_zero]
  rw [h, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
