module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUnitModel

/-! 複体から実 Hom への入力は、単位 Hom 同型の逆を含む同じ一つの鎖写像で表示できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]

lemma dgGluingPinchedComplexModelIso_inv (x y : E) :
    (pinchedComplexModelIso x y).inv =
      pinchedHomChainMap (D := DGComplexPinchedModel.{u, v} (homObject R E x y)) (E := E)
        (x := complexPinchedSource _) (y := complexPinchedTarget _) (x' := x) (y' := y)
        (complexUnitHomIso (homObject R E x y)).inv := by
  apply (cancel_mono (pinchedComplexModelIso x y).hom).1
  rw [Iso.inv_hom_id, dgGluingPinchedComplexModelIso_hom, ← pinchedHomChainMap_comp,
    Iso.inv_hom_id, pinchedHomChainMap_id]

lemma dgGluingComplexPinchedInput_eq_chainMap {K : Complex R} {x y : E}
    (φ : K ⟶ homObject R E x y) :
    complexPinchedMap.{u, v} φ ≫ (pinchedComplexModelIso x y).inv =
      pinchedHomChainMap (D := DGComplexPinchedModel.{u, v} K) (E := E)
        (x := complexPinchedSource _) (y := complexPinchedTarget _) (x' := x) (y' := y)
        ((complexUnitHomIso K).inv ≫ φ) := by
  have h : homPostcompose (𝟙_ (Complex R)) φ ≫
      (complexUnitHomIso (homObject R E x y)).inv = (complexUnitHomIso K).inv ≫ φ := by
    rw [complexUnitHomPostcompose_eq, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [complexPinchedMap, dgGluingPinchedComplexModelIso_inv, ← pinchedHomChainMap_comp]
  exact congrArg (fun f : homComplex R (𝟙_ (Complex R)) K ⟶ homObject R E x y =>
    pinchedHomChainMap (D := DGComplexPinchedModel.{u, v} K) (E := E)
      (x := complexPinchedSource _) (y := complexPinchedTarget _) (x' := x) (y' := y) f) h

end SerrePositivity.InfinityCategories
