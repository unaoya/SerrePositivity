module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationDegenerateCoefficient
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 相零から相一で切る同じ実補正は、I 上非単射な引き戻しで零。 -/
lemma dgModuleAugmentationHomotopyCut_pullback_zero_of_not_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1))))
    (j : Fin (m + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hpa : β (α a) = 0) (hpj : β (α j) = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F (s.pullback α) I a b k j = 0 := by
  have hamin : IsLeast (I : Set (Fin (m + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (m + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hIL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hIR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have haL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hIL)
  have hjL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hIL)
  have hjR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hIR)
  have hbR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hIR)
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (s.pullback α) _ _ _ _ hIR hjR hbR rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (s.pullback α) _ _ _ _ hIL haL hjL rfl]
  by_cases hiR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1)))
  · have hiL : ¬ Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))) := by
      intro h
      exact hi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCut_injective_glue α I j hj h hiR)
    have hcL : (I.filter (· ≤ j)).card ≠ 2 := by
      intro hc
      have hmin : IsLeast ((I.filter (· ≤ j)) : Set (Fin (m + 1))) a :=
        ⟨Finset.mem_filter.mpr ⟨hamin.1, haj.le⟩, fun x hx ↦
          hamin.2 (Finset.mem_filter.mp hx).1⟩
      have hmax : IsGreatest ((I.filter (· ≤ j)) : Set (Fin (m + 1))) j :=
        ⟨Finset.mem_filter.mpr ⟨hj, le_refl j⟩, fun _ hx ↦ (Finset.mem_filter.mp hx).2⟩
      have he := congrArg β (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hiL hc hmin hmax)
      rw [hpa, hpj] at he
      exact (show (0 : Fin 2) ≠ 1 from by decide) he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α (I.filter (· ≤ j)) a j _ hIL haL hjL
      rfl hiL hcL, map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent_pullback_zero_of_not_inj R C E F s α
      (I.filter (j ≤ ·)) j b _ hIR hjR hbR rfl hiR, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
