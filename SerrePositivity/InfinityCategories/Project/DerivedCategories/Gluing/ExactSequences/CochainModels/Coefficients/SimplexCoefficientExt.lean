module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! 対象と全次数の係数の異種等号から、元の単体全体の厳密な等号へ戻す。 -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open DifferentialGraded
variable {R : Type u} [CommRing R] {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingSimplexData_ext_coefficients {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R E n)
    (ho : ∀ i, s.obj i = t.obj i)
    (hh : ∀ I a b k hI ha hb hk,
      HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk)) : s = t := by
  rcases s with ⟨so, sh⟩
  rcases t with ⟨tobj, th⟩
  have hobj : so = tobj := funext ho
  subst tobj
  have hhom : sh = th := by
    funext I a b k hI ha hb hk
    exact eq_of_heq (hh I a b k hI ha hb hk)
  cases hhom
  rfl

lemma dgGluingSimplex_ext_coefficients {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E n)
    (ho : ∀ i, s.obj i = t.obj i)
    (hh : ∀ I a b k hI ha hb hk,
      HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk)) : s = t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexData_ext_coefficients s.toSimplexData t.toSimplexData ho hh)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
