module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! 次数表示の異種等号を保持して、線形射影による符号付き補正の消滅を回収する。 -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded

lemma dgGluingGradedHom_zero_heq {R : Type u} [CommRing R]
    {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {x y x' y' : E} {p q : ℤ}
    (hx : x = x') (hy : y = y') (hp : p = q) :
    HEq (0 : GradedHom R x y p) (0 : GradedHom R x' y' q) := by
  cases hx
  cases hy
  cases hp
  rfl

lemma dgGluingComplexMap_zero_of_scalar_heq {R : Type u} [CommRing R]
    {K L : _root_.SerrePositivity.DifferentialGraded.Complex R} (f : K ⟶ L) {p q : ℤ} (hp : p = q)
    (a : K.X p) (b : K.X q) (σ : ℤˣ) (ha : HEq a (σ • b)) (hb : f.f q b = 0) :
    f.f p a = 0 := by
  cases hp
  rw [eq_of_heq ha]
  simp only [Units.smul_def, map_zsmul, hb, zsmul_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
