module
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison

/-! 複体自身の単位 Hom への移送は、同じ pinched 模型の比較同型で相殺する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R]

lemma dgGluingPinchedComplexModelIso_hom {E : Type v} [DGCategory R E] (x y : E) :
    (pinchedComplexModelIso x y).hom =
      pinchedHomChainMap (complexUnitHomIso (homObject R E x y)).hom := rfl

lemma dgGluingComplexPinchedUnitHom_model (L : Complex R) :
    complexPinchedMap.{u, v} (complexUnitHomIso L).hom =
      (pinchedComplexModelIso (complexPinchedSource.{u, v} L)
        (complexPinchedTarget L)).hom := by
  have h : homPostcompose (𝟙_ (Complex R)) (complexUnitHomIso L).hom =
      (complexUnitHomIso (homComplex R (𝟙_ (Complex R)) L)).hom := by
    apply (cancel_epi (complexUnitHomIso L).hom).1
    exact complexUnitHomIso_naturality (complexUnitHomIso L).hom
  rw [dgGluingPinchedComplexModelIso_hom]
  exact congrArg (fun f : homComplex R (𝟙_ (Complex R)) L ⟶
      homComplex R (𝟙_ (Complex R)) (homComplex R (𝟙_ (Complex R)) L) =>
    pinchedHomChainMap (D := DGComplexPinchedModel.{u, v} L)
      (E := DGComplexPinchedModel.{u, v} (homComplex R (𝟙_ (Complex R)) L))
      (x := complexPinchedSource L) (y := complexPinchedTarget L)
      (x' := complexPinchedSource _) (y' := complexPinchedTarget _) f) h

lemma dgGluingComplexPinchedUnitHom_cancel {K L : Complex R} (f : K ⟶ L) :
    complexPinchedMap.{u, v} (f ≫ (complexUnitHomIso L).hom) ≫
      (pinchedComplexModelIso (complexPinchedSource.{u, v} L)
        (complexPinchedTarget L)).inv = complexPinchedMap.{u, v} f := by
  rw [complexPinchedMap_comp, Category.assoc, dgGluingComplexPinchedUnitHom_model,
    Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
