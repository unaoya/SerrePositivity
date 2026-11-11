module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSourceRefinementLinear
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEqualityTransport

/-! # 零を固定する番号変更と始点細分の Hom 写像

概要：零を固定し正番号を正番号へ送る番号変更は、同じ閉始点細分の Hom 写像と両立する。
方針：番号関数を零と tail に分けて始対象の輸送を消去し、成分の異種等号で比較する。
規約：任意の次数を保つ。使われ方：始点を含む単射面と閉始点細分の可換性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {n : ℕ} (o : Fin (n + 1) → D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (o 0))

/-- 正始点・正終点の Hom の写像は元の成分と異種等号で一致する。 -/
lemma dgSourceRefinementHomLinear_heq_of_ne_zero (a b : Fin (n + 1))
    (ha : a ≠ 0) (hb : b ≠ 0) (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o a) (o b) k) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s a b k f) f :=
  (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D o q s a b ha hb k f)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _)

/-- 零始点・正終点の Hom の写像は同じ閉前合成と異種等号で一致する。 -/
lemma dgSourceRefinementHomLinear_heq_from_zero (b : Fin (n + 1)) (hb : b ≠ 0)
    (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o 0) (o b) k) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s 0 b k f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k f s) :=
  (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_from_zero A D o q s b hb k f)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _)

omit [CommRing A] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] in
/-- 零を固定し正番号を正番号へ送る番号変更は、新しい対象族と両立する。 -/
lemma dgSourceRefinementObj_reindex {m : ℕ} (α : Fin (m + 1) → Fin (n + 1))
    (h₀ : α 0 = 0) (hz : ∀ i, i ≠ 0 → α i ≠ 0) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj D o q (α i) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj D (o ∘ α) q i := by
  by_cases hi : i = 0
  · subst i
    simp only [h₀, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj, ite_true]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj, ite_eq_right hi, ite_eq_right (hz i hi), Function.comp_apply]

/-- 同じ閉射を零固定式で輸送すると、制限の Hom 写像と元の Hom 写像は一致する。 -/
lemma dgSourceRefinementHomLinear_reindex {m : ℕ} (α : Fin (m + 1) → Fin (n + 1))
    (h₀ : α 0 = 0) (hz : ∀ i, i ≠ 0 → α i ≠ 0)
    (a b : Fin (m + 1)) (hb : b ≠ 0) (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o (α a)) (o (α b)) k) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D o q s (α a) (α b) k f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D (o ∘ α) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (congrArg o h₀.symm)) a b k f) := by
  obtain ⟨z, β, rfl⟩ := Fin.exists_cons α
  change z = 0 at h₀
  subst z
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id]
  by_cases ha : a = 0
  · subst a
    exact (dgSourceRefinementHomLinear_heq_from_zero A D o q s _ (hz b hb) k f).trans
      (dgSourceRefinementHomLinear_heq_from_zero A D (o ∘ Fin.cons 0 β) q s b hb k f).symm
  · exact (dgSourceRefinementHomLinear_heq_of_ne_zero A D o q s _ _ (hz a ha) (hz b hb) k f).trans
      (dgSourceRefinementHomLinear_heq_of_ne_zero A D (o ∘ Fin.cons 0 β) q s a b ha hb k f).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
