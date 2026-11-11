module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison

/-! 複体自身の単位 Hom への移送は、同じ pinched 模型の比較同型で相殺する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R]

lemma dgGluingPinchedComplexModelIso_hom {E : Type v} [DGCategory R E] (x y : E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homObject R E x y)).hom := rfl

lemma dgGluingComplexPinchedUnitHom_model (L : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, v} L)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)).hom := by
  have h : homPostcompose (𝟙_ (Complex R)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homComplex R (𝟙_ (Complex R)) L)).hom := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom).1
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom
  rw [dgGluingPinchedComplexModelIso_hom]
  exact congrArg (fun f : homComplex R (𝟙_ (Complex R)) L ⟶
      homComplex R (𝟙_ (Complex R)) (homComplex R (𝟙_ (Complex R)) L) =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} L)
      (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} (homComplex R (𝟙_ (Complex R)) L))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
      (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) f) h

lemma dgGluingComplexPinchedUnitHom_cancel {K L : Complex R} (f : K ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, v} L)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)).inv = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Category.assoc, dgGluingComplexPinchedUnitHom_model,
    Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
