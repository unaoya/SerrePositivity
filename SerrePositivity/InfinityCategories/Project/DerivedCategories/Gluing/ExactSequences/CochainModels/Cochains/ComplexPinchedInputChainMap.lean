module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPinchedUnitModel

/-! 複体から実 Hom への入力は、単位 Hom 同型の逆を含む同じ一つの鎖写像で表示できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]

lemma dgGluingPinchedComplexModelIso_inv (x y : E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} (homObject R E x y)) (E := E)
        (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) (x' := x) (y' := y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homObject R E x y)).inv := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom).1
  rw [Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedComplexModelIso_hom, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp,
    Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id]

lemma dgGluingComplexPinchedInput_eq_chainMap {K : Complex R} {x y : E}
    (φ : K ⟶ homObject R E x y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} K) (E := E)
        (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) (x' := x) (y' := y)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ φ) := by
  have h : homPostcompose (𝟙_ (Complex R)) φ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homObject R E x y)).inv = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ φ := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomPostcompose_eq, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap, dgGluingPinchedComplexModelIso_inv, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]
  exact congrArg (fun f : homComplex R (𝟙_ (Complex R)) K ⟶ homObject R E x y =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} K) (E := E)
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) (x' := x) (y' := y) f) h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
