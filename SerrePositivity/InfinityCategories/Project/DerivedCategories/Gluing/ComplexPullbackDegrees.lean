module
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! 複体の実引き戻しを各整数次数の元の持ち上げと一意性として読む。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q T U : Complex R}
  {a : P ⟶ Q} {b : P ⟶ T} {f : Q ⟶ U} {g : T ⟶ U}

lemma dgGluingComplexPullback_degree (h : IsPullback a b f g) (n : ℤ) :
    IsPullback ((CategoryTheory.forget (ModuleCat R)).map (a.f n))
      ((CategoryTheory.forget (ModuleCat R)).map (b.f n))
      ((CategoryTheory.forget (ModuleCat R)).map (f.f n))
      ((CategoryTheory.forget (ModuleCat R)).map (g.f n)) :=
  (h.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n)).map
    (CategoryTheory.forget (ModuleCat R))

lemma dgGluingComplexPullback_ext (h : IsPullback a b f g) (n : ℤ) {s t : P.X n}
    (ha : a.f n s = a.f n t) (hb : b.f n s = b.f n t) : s = t :=
  Types.ext_of_isPullback (dgGluingComplexPullback_degree h n) ha hb

lemma dgGluingComplexPullback_exists (h : IsPullback a b f g) (n : ℤ)
    (s : Q.X n) (t : T.X n) (hst : f.f n s = g.f n t) :
    ∃ z : P.X n, a.f n z = s ∧ b.f n z = t :=
  Types.exists_of_isPullback (dgGluingComplexPullback_degree h n) s t hst

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
