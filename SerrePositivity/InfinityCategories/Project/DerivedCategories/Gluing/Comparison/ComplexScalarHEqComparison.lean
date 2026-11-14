module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexLinearHEq

/-! 共通の次数表示に移して、二つの符号付き補正を実鎖写像で比較する。 -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded

lemma dgGluingComplexMap_scalar_heq {R : Type u} [CommRing R]
    {K L : Complex R} (f : K ⟶ L) {p q : ℤ} (hp : p = q)
    (a : K.X p) (b : K.X q) (c : L.X p) (d : L.X q) (σ : ℤˣ)
    (ha : HEq a (σ • b)) (hc : HEq c (σ • d)) (hb : f.f q b = d) :
    f.f p a = c := by
  cases hp
  rw [eq_of_heq ha, eq_of_heq hc]
  simp only [Units.smul_def, map_zsmul, hb]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
