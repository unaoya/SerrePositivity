module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.WeightedVertexInversions

/-!
模型。文献の定義との比較は後で
# 別々の活動集合の逆転寄与を水平 fiber で数える

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
元の二つの有限和を、水平座標ごとの濃度の積へ書き直す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 二つの有限集合の元の逆転寄与を水平 fiber ごとにまとめる（BF §2.2.4）。 -/
lemma sum_positionInversionTerm_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (S T : Finset (Fin N)) :
    (∑ x ∈ S, ∑ y ∈ T, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (v ∘ f) x y) =
      ∑ i : Fin M, ∑ j : Fin M, if i < j ∧ v j < v i then
        (S.filter (fun x => f x = i)).card * (T.filter (fun y => f y = j)).card else 0 := by
  have hy (x : Fin N) : (∑ y ∈ T, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (v ∘ f) x y) =
      ∑ j : Fin M, if f x < j ∧ v j < v (f x) then (T.filter (fun y => f y = j)).card else 0 := by
    have h := Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.univ) (g := f)
      (fun _ _ => Finset.mem_univ _) (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (v ∘ f) x y)
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    have hc : ∀ y ∈ T.filter (fun y => f y = j),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (v ∘ f) x y =
          if f x < j ∧ v j < v (f x) then 1 else 0 := by
      intro y hy
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionInversionTerm_comp_monotone, (Finset.mem_filter.mp hy).2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const]
    split_ifs <;> simp
  simp_rw [hy]
  have h := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.univ) (g := f)
    (fun _ _ => Finset.mem_univ _) (fun x =>
      ∑ j : Fin M, if f x < j ∧ v j < v (f x) then (T.filter (fun y => f y = j)).card else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ∀ x ∈ S.filter (fun x => f x = i),
      (∑ j : Fin M, if f x < j ∧ v j < v (f x) then (T.filter (fun y => f y = j)).card else 0) =
      ∑ j : Fin M, if i < j ∧ v j < v i then (T.filter (fun y => f y = j)).card else 0 := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
