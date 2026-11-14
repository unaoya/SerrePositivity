module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalSingletons
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryTerms
public import SerrePositivity.EInfinity.Surjection.Deletion

/-!
# 非全射な水平削除の元の境界項は零

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
既存の削除語の全射性の判定を、水平な一頂点のfiberと出力次数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open scoped Simplicial
universe u
variable (A : Type u) [CommRing A]

/-- C205：非全射な水平削除で消える色は一度しか現れず、その出力次数は零。 -/
lemma outputDegree_zero_horizontal_of_not_surjective {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k))) :
    outputDegree s v (label s v.val k) = 0 := by
  have hu : ∀ i, v.val i = v.val (s.horizontal k) → i = s.horizontal k := by
    intro i hi
    by_contra hne
    exact hns ((Surjection.erase_surjective_iff v.val v.surjective _).mpr ⟨i, hne, hi⟩)
  have hsingle := (horizontal_fiber_singleton_iff s k).mpr hk
  have hc : colorPositions s v.val (label s v.val k) = {k} := by
    ext j
    constructor
    · intro hj
      apply Finset.mem_singleton.mpr
      apply hsingle j
      exact hu _ (Finset.mem_filter.mp hj).2
    · intro hj
      exact Finset.mem_singleton.mp hj ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  unfold outputDegree
  rw [hc, Finset.card_singleton]

/-- C206：同じ非全射な水平削除の元の境界項は、定義どおり零となる。 -/
lemma outputBoundaryTerm_horizontal_not_surjective {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (hk : HorizontalVertex s k)
    (hns : ¬Function.Surjective (Surjection.erase v.val (s.horizontal k)))
    (j : Fin (outputDegree s v (label s v.val k) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x = 0 := by
  unfold outputBoundaryTerm
  apply dite_eq_right
  rw [outputDegree_zero_horizontal_of_not_surjective s v k hk hns]
  omega

end SerrePositivity.EInfinity.SimplexCuts
