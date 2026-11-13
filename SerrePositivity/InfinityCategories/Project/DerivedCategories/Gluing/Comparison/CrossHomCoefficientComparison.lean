module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.CoconeBottomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaBottomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.CrossHom.CrossHomCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomComparison

/-! native の同じ係数包含は、全 Yoneda 同型によって comma の標準包含に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M)

lemma dgGluingCrossHomCoefficientMap_comma :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Y.val).hom =
    (dgYonedaIso R X.val.left (M.rightAt Y.val.right)).inv⟦(-1 : ℤ)⟧' ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBottomInclusion R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeBottomInclusion_naturality _ _ _ _ (by
    apply (cancel_mono (dgYonedaIso R X.val.left (M.rightAt Y.val.right)).hom).1
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDifference_yoneda R C D M X.val Y.val).symm)

lemma dgGluingCrossHomCoefficientMap_comma_apply (n : ℤ)
    (t : ((M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧).X n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X.val Y.val).hom.f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Y).f n t) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBottomInclusion R D (RightModule R C) M.toFunctor
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y.val)).f n
      ((dgYonedaIso R X.val.left (M.rightAt Y.val.right)).inv.f (n - 1) t) := by
  have h := congrArg (fun k => k.f n t)
    (dgGluingCrossHomCoefficientMap_comma R C D M X Y)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    CochainComplex.shiftFunctor_map_f'] using! h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
