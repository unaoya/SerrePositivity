module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ReplacementLocality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # 最上位の一射による dg 単体データの完成

概要：真部分集合の方程式と、正しい微分を持つ最上位の一射から実単体を作る。
方針：固定一射の置換と局所性で全方程式・全面の保存を検証する。
規約：持ち上げや収縮の選び方と独立。使われ方：β3 の相対境界充填。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 正しい最上位の一射を挿入し、全方程式を持つ dg 単体へ完成する。 -/
def dgCompleteTopSimplex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ))
    (q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k)
    (dq : _root_.SerrePositivity.DifferentialGraded.differential A q = s.rhs Finset.univ a b k hI ha hb hk) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1) where
  toSimplexData := s.replaceFixed Finset.univ a b k hI ha hb hk q
  equation I := by
    by_cases hfull : I = Finset.univ
    · subst I
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed _ Finset.univ a b k hI ha hb hk
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_hom_same, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]
      exact dq
    · exact s.equation_replace_of_not_subset _ _ I
        (fun hn => hfull (le_antisymm (Finset.subset_univ I) hn)) (he I hfull)

/-- 最上位の一射による完成は全ての面を保つ。 -/
lemma dgCompleteTopSimplex_pullback_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ))
    (q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k)
    (dq : _root_.SerrePositivity.DifferentialGraded.differential A q = s.rhs Finset.univ a b k hI ha hb hk) (j : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompleteTopSimplex s he a b k hI ha hb hk q dq).toSimplexData.pullback
        j.succAboveOrderEmb.toOrderHom = s.pullback j.succAboveOrderEmb.toOrderHom :=
  s.replace_pullback_of_omits _ _ _ j (Finset.mem_univ j) (Fin.succAbove_ne j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
