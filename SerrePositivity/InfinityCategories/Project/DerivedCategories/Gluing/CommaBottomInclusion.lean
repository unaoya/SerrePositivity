module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeBottomComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaComparison

/-! comma の同じ Hom 複体への標準 bottom 包含と、その全次数の三成分。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)

def dgGluingCommaBottomInclusion :
    (homObject R E X.replacement (F.obj Y.source))⟦(-1 : ℤ)⟧ ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)

lemma dgGluingCommaBottomInclusion_source :
    dgGluingCommaBottomInclusion R C E F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y = 0 := by
  simp only [dgGluingCommaBottomInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_fst, zero_comp]

lemma dgGluingCommaBottomInclusion_replacement :
    dgGluingCommaBottomInclusion R C E F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y = 0 := by
  simp only [dgGluingCommaBottomInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_fst, zero_comp]

lemma dgGluingCommaBottomInclusion_primitive (n : ℤ) :
    (dgGluingCommaBottomInclusion R C E F X Y).f n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega) = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_snd _ n

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
