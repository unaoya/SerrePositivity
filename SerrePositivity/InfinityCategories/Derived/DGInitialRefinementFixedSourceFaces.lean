module
public import SerrePositivity.InfinityCategories.Derived.DGSourceRefinementReindex
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementComponents

/-! # 始点を含む単射面と閉始点細分の可換性

概要：零を固定する任意の順序単射の制限と、同じ閉始点細分は厳密に可換。
方針：対象ごとの番号変更と、単射の像の各斉次成分を異種等号で比較する。
規約：始対象の閉射を零固定式で輸送する。使われ方：高次ホーンの指定面の重なり。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 零を固定する順序単射の制限は、実データの同じ閉始点細分と厳密に可換。 -/
lemma dgSimplexDataInitialRefinement_pullback_fixed_zero {m n : ℕ} (t : SimplexData A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (h₀ : α 0 = 0) :
    (dgSimplexDataInitialRefinement A D t q s).pullback α =
      dgSimplexDataInitialRefinement A D (t.pullback α) q
        (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  have hz (i : Fin (m + 1)) (hi : i ≠ 0) : α i ≠ 0 := by
    intro he
    exact hi (hα (he.trans h₀.symm))
  apply dgSimplexData_ext_of_components A D
  · intro i
    exact dgSourceRefinementObj_reindex D t.obj q α h₀ hz i
  · intro I a b k hI ha hb hk
    have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a)
      (dgSimplexIndex_endpoints_lt I a b hI ha hb))
    dsimp only [dgSimplexDataInitialRefinement]
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn,
      SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn]
    exact dgSourceRefinementHomLinear_reindex A D t.obj q s α h₀ hz a b hb0 k _

/-- 零を固定する順序単射の制限は、実単体の同じ閉始点細分と厳密に可換。 -/
lemma dgSimplexInitialRefinement_pullback_fixed_zero {m n : ℕ} (t : Simplex A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (h₀ : α 0 = 0) :
    (dgSimplexInitialRefinement A D t q s).pullback α =
      dgSimplexInitialRefinement A D (t.pullback α) q
        (dgClosedTargetTransport A D s (congrArg t.obj h₀.symm)) := by
  apply Simplex.ext
  exact dgSimplexDataInitialRefinement_pullback_fixed_zero A D t.toSimplexData q s α hα h₀

end SerrePositivity.InfinityCategories
