module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedComplexModelComparison

/-! 複体の実空間模型から元の pinched Hom へ戻す同型も、同じ Hom 鎖写像を保つ。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C D : Type v} [DGCategory R C] [DGCategory R D]

lemma dgGluingComplexPinchedModelInverse_naturality {x y : C} {x' y' : D}
    (f : homObject R C x y ⟶ homObject R D x' y') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').inv =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f := by
  have h := congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv ≫ k ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').inv) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso_naturality f)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
