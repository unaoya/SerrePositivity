module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexLinearHEq
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMinusOneCochainBoundary

/-! 同じ比較 cochain の出力次数の算術表示替えは、実後合成と符号を含め異種等号で一致する。 -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex

lemma dgGluingCochain_post_smul_heq {R : Type u} [CommRing R]
    {K L Q : Complex R} (h : Cochain K L (-1)) (f : L ⟶ Q)
    {p q q' : ℤ} (hq : q = q') (a : K.X p) (hp : p + -1 = q) (hp' : p + -1 = q')
    (σ : ℤˣ) :
    HEq (σ • f.f q (h.v p q hp a)) (σ • f.f q' (h.v p q' hp' a)) := by
  cases hq
  rfl

lemma dgGluingCochain_neg_smul_heq {R : Type u} [CommRing R]
    {K L : Complex R} (h : Cochain K L (-1))
    {p q q' : ℤ} (hq : q = q') (a : K.X p) (hp : p + -1 = q) (hp' : p + -1 = q')
    (σ : ℤˣ) :
    HEq (σ • -h.v p q hp a) (σ • -h.v p q' hp' a) := by
  cases hq
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
