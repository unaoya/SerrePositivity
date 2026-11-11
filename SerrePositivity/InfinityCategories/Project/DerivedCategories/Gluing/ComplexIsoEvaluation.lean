module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainUnitHomCancellation

/-! 複体同型の逆・順方向の合成は、全次数で元の値を厳密に回収する。 -/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded HomologicalComplex

lemma dgGluingComplexIso_inv_hom_apply {R : Type u} [CommRing R]
    {K L : Complex R} (e : K ≅ L) (k : ℤ) (a : L.X k) :
    e.hom.f k (e.inv.f k a) = a :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.inv_hom_id k) a

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
