module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.GradedPostcompositionClosed

/-! 始域・標的を実 comma Hom に固定した全次数の後合成。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z W : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)

/-- 元の三つの comma Hom 複体を指定した、同じ全次数の後合成。 -/
def dgGluingCommaGradedPostcomposition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z ⟶
      homComplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) X Y Z

/-- 指定した閉 comma 射で移した元の作用は、作用後に同じ閉射で後合成したもの。 -/
abbrev dgGluingCommaGradedPostcomposition_postcompose
    (a : ForgetEnrichment.of (Complex R) Z ⟶ ForgetEnrichment.of (Complex R) W)
    (g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z).X (-1)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition_postcompose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    X Y Z W a g).symm

/-- 試験複体からの閉前合成を含めた、同じ後合成の結合則。 -/
abbrev dgGluingCommaGradedPostcomposition_pre_post
    (a : ForgetEnrichment.of (Complex R) Z ⟶ ForgetEnrichment.of (Complex R) W)
    (g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z).X (-1))
    (P : Complex R) (b : P ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y) :=
  let h := dgGluingCommaGradedPostcomposition_postcompose R C E F X Y Z W a g
  let hh := congrArg (fun k => (Cochain.ofHom b).comp k (zero_add (-1))) h
  hh.trans (Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom b)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) X Y Z).f (-1) g)
    (Cochain.ofHom (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) a))
    (add_zero (-1))).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
