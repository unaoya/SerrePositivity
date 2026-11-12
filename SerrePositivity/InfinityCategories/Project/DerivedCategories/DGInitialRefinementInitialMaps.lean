module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSourceRefinementReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplexComponentExt
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 初期頂点だけを零へ送る一般順序写像と閉始点細分

概要：零固定・正番号非零の一般順序写像による制限と、同じ閉始点細分は厳密に可換。
方針：各成分を像上単射・非単射零・潰れた二点の単位へ分け、正対象の単位を比較する。
規約：非単射も含む。使われ方：正番号退化と実錐の閉細分の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]


/-- 初期頂点だけを零へ送る順序写像による制限は、同じ実データの閉始点細分と可換。 -/
lemma dgSimplexDataInitialRefinement_pullback_initial {m n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (h₀ : α 0 = 0)
    (hz : ∀ i, i ≠ 0 → α i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D (t.pullback α) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A D
  · intro i
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_reindex D t.obj q α h₀ hz i
  · intro I a b k hI ha hb hk
    have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexIndex_endpoints_lt I a b hI ha hb))
    by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
    · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_reindex A D t.obj q s α h₀ hz a b hb0 k _
    · by_cases hc : I.card = 2
      · have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
          (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
        have ha0 : a ≠ 0 := by
          intro he
          exact hz b hb0 (hab.symm.trans ((congrArg α he).trans h₀))
        have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s) α I a b k hI ha hb hk hi hc
        have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_hom_ne_zero A D (t.pullback α) q
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) I a b k hI ha hb hk ha0
        have hu : ∀ x y : D, x = y → HEq (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val := by
          intro x y h
          cases h
          rfl
        exact hl.trans ((hu _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D t.obj q (α b) (hz b hb0))).trans
          ((t.pullback_hom_of_collapsed_pair α I a b k hI ha hb hk hi hc).symm.trans hr.symm))
      · have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s) α I a b k hI ha hb hk hi hc
        have hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D (t.pullback α) q
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj h₀.symm))).hom I a b k hI ha hb hk =
            0 := by
          change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D (t.pullback α).obj q
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) a b k
              ((t.pullback α).hom I a b k hI ha hb hk) = 0
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc, map_zero]
        exact (heq_of_eq hl).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_reindex D t.obj q α h₀ hz a)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_reindex D t.obj q α h₀ hz b) rfl).trans (heq_of_eq hr).symm)

/-- 初期頂点だけを零へ送る一般順序写像による実単体の制限も、同じ閉始点細分と可換。 -/
lemma dgSimplexInitialRefinement_pullback_initial {m n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (h₀ : α 0 = 0)
    (hz : ∀ i, i ≠ 0 → α i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D (t.pullback α) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgSimplexDataInitialRefinement_pullback_initial A D t.toSimplexData q s α h₀ hz

end SerrePositivity.InfinityCategories.Project.DerivedCategories
