module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugDegenerateCoefficient
/-!
概要：非単射な引き戻しの同じ混合切断補正が零になることを証明する。
方針：右が非単射なら比較の単位零を使い、左だけ非単射なら混合相で潰れた辺を除く。
規約：添字集合の外の挙動は任意。使われ方：高次退化の全補正和の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {m n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 相零から相一で切る同じ実補正は、I 上非単射な引き戻しで零。 -/
lemma dgCommaAugmentationHomotopyCut_pullback_zero_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (j : Fin (m + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hpa : β (α a) = 0) (hpj : β (α j) = 1) :
    dgCommaAugmentationHomotopyCut R C E F (s.pullback α) I a b k j = 0 := by
  have hamin : IsLeast (I : Set (Fin (m + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (m + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hIL := Index.left_two hamin.1 hj haj
  have hIR := Index.right_two hj hbmax.1 hjb
  have haL := Index.left_min hamin haj.le (Index.nonempty hIL)
  have hjL := Index.left_max hj (Index.nonempty hIL)
  have hjR := Index.right_min hj (Index.nonempty hIR)
  have hbR := Index.right_max hbmax hjb.le (Index.nonempty hIR)
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := Index.split_card hj
    omega
  rw [dgCommaAugmentationHomotopyCut, dite_eq_left hsum,
    SimplexData.homOrZero_eq (s.pullback α) _ _ _ _ hIR hjR hbR rfl,
    SimplexData.homOrZero_eq (s.pullback α) _ _ _ _ hIL haL hjL rfl]
  by_cases hiR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1)))
  · have hiL : ¬ Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))) := by
      intro h
      exact hi (dgModuleAugmentationCut_injective_glue α I j hj h hiR)
    have hcL : (I.filter (· ≤ j)).card ≠ 2 := by
      intro hc
      have hmin : IsLeast ((I.filter (· ≤ j)) : Set (Fin (m + 1))) a :=
        ⟨Finset.mem_filter.mpr ⟨hamin.1, haj.le⟩, fun x hx ↦
          hamin.2 (Finset.mem_filter.mp hx).1⟩
      have hmax : IsGreatest ((I.filter (· ≤ j)) : Set (Fin (m + 1))) j :=
        ⟨Finset.mem_filter.mpr ⟨hj, le_refl j⟩, fun _ hx ↦ (Finset.mem_filter.mp hx).2⟩
      have he := congrArg β (Index.collapse_two hiL hc hmin hmax)
      rw [hpa, hpj] at he
      exact (show (0 : Fin 2) ≠ 1 from by decide) he
    rw [SimplexData.pullback_hom_of_not_inj s α (I.filter (· ≤ j)) a j _ hIL haL hjL
      rfl hiL hcL, map_zero, compose_zero]
  · rw [dgCommaAugmentationHomotopyComponent_pullback_zero_of_not_inj R C E F s α
      (I.filter (j ≤ ·)) j b _ hIR hjR hbR rfl hiR, zero_compose]
end SerrePositivity.InfinityCategories
