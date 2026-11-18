module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryOutputCutEquiv

/-!
模型。文献の定義との比較は後で
# 一出現の実際の零次出力による全Cut和の再添字

Berger–Fresse §2.2.6、M14 L12a、報告 §353。
元の全Cut和を零次出力の部分型とその零となる補集合に分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の一点挿入と実際の零次出力の同値による全有限和の一致（BF §2.2.6）。 -/
lemma sum_nullaryOutputCuts {M : Type*} [AddCommMonoid M] {m q r : ℕ}
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (p : Fin (m + 2)) (k : Fin r)
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (F : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q → M) (G : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q → M)
    (hpair : ∀ t, F t = G (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut t p))
    (hzero : ∀ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k ≠ 0 → G s = 0) :
    ∑ t, F t = ∑ s, G s := by
  let e := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOutputCutEquiv m q r v p k hp hu
  have hc : (∑ s : {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q // ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0}, G s.val) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    exact hzero s.val s.property
  have hs := Fintype.sum_subtype_add_sum_subtype (fun s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0) G
  rw [hc, add_zero] at hs
  calc
    ∑ t, F t = ∑ t, G (e t).val := by
      apply Finset.sum_congr rfl
      intro t _
      exact hpair t
    _ = ∑ s : {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0}, G s.val :=
      e.sum_comp (fun s => G s.val)
    _ = _ := hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
