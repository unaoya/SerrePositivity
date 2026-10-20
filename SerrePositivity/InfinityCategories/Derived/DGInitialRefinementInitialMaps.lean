module
public import SerrePositivity.InfinityCategories.Derived.DGSourceRefinementReindex
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementComponents
public import SerrePositivity.InfinityCategories.Derived.DGSimplexComponentExt
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]


/-- 初期頂点だけを零へ送る順序写像による制限は、同じ実データの閉始点細分と可換。 -/
lemma dgSimplexDataInitialRefinement_pullback_initial {m n : ℕ} (t : SimplexData A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (h₀ : α 0 = 0)
    (hz : ∀ i, i ≠ 0 → α i ≠ 0) :
    (dgSimplexDataInitialRefinement A D t q s).pullback α =
      dgSimplexDataInitialRefinement A D (t.pullback α) q
        (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  apply dgSimplexData_ext_of_components A D
  · intro i
    exact dgSourceRefinementObj_reindex D t.obj q α h₀ hz i
  · intro I a b k hI ha hb hk
    have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a)
      (dgSimplexIndex_endpoints_lt I a b hI ha hb))
    by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
    · dsimp only [dgSimplexDataInitialRefinement]
      rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      exact dgSourceRefinementHomLinear_reindex A D t.obj q s α h₀ hz a b hb0 k _
    · by_cases hc : I.card = 2
      · have hab : α a = α b := Index.collapse_two hi hc
          (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
        have ha0 : a ≠ 0 := by
          intro he
          exact hz b hb0 (hab.symm.trans ((congrArg α he).trans h₀))
        have hl := SimplexData.pullback_hom_of_collapsed_pair
          (dgSimplexDataInitialRefinement A D t q s) α I a b k hI ha hb hk hi hc
        have hr := dgSimplexDataInitialRefinement_hom_ne_zero A D (t.pullback α) q
          (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) I a b k hI ha hb hk ha0
        have hu : ∀ x y : D, x = y → HEq (unitElement A x).val (unitElement A y).val := by
          intro x y h
          cases h
          rfl
        exact hl.trans ((hu _ _ (dgSourceRefinementObj_ne_zero D t.obj q (α b) (hz b hb0))).trans
          ((t.pullback_hom_of_collapsed_pair α I a b k hI ha hb hk hi hc).symm.trans hr.symm))
      · have hl := SimplexData.pullback_hom_of_not_inj
          (dgSimplexDataInitialRefinement A D t q s) α I a b k hI ha hb hk hi hc
        have hr : (dgSimplexDataInitialRefinement A D (t.pullback α) q
            (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm))).hom I a b k hI ha hb hk =
            0 := by
          change dgSourceRefinementHomLinear A D (t.pullback α).obj q
            (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) a b k
              ((t.pullback α).hom I a b k hI ha hb hk) = 0
          rw [SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc, map_zero]
        exact (heq_of_eq hl).trans ((gradedHom_zero_heq
          (dgSourceRefinementObj_reindex D t.obj q α h₀ hz a)
          (dgSourceRefinementObj_reindex D t.obj q α h₀ hz b) rfl).trans (heq_of_eq hr).symm)

/-- 初期頂点だけを零へ送る一般順序写像による実単体の制限も、同じ閉始点細分と可換。 -/
lemma dgSimplexInitialRefinement_pullback_initial {m n : ℕ} (t : Simplex A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (h₀ : α 0 = 0)
    (hz : ∀ i, i ≠ 0 → α i ≠ 0) :
    (dgSimplexInitialRefinement A D t q s).pullback α =
      dgSimplexInitialRefinement A D (t.pullback α) q
        (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  apply Simplex.ext
  exact dgSimplexDataInitialRefinement_pullback_initial A D t.toSimplexData q s α h₀ hz

end SerrePositivity.InfinityCategories
