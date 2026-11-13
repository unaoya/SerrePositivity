module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.UniverseTransport.UniverseHomModelNaturality

/-! 実 Hom 作用を複体模型へ移すと、元の鎖写像の作用と宇宙変更だけが残る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : C} {x' y' : D}

def dgGluingUniverseHomModelComparison
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') :
    (SSet.uliftFunctor.{max u v w r, max u v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (homObject R C x y)) ⟶
      (SSet.uliftFunctor.{max u v w r, max u w}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, w} (homObject R D x' y')) :=
  (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, max u v w r} φ ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').hom

lemma dgGluingUniverseHomModelComparison_eq
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') :
    dgGluingUniverseHomModelComparison.{u, v, w, r} φ =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} (homObject R D x' y')).hom := by
  rw [dgGluingUniverseHomModelComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomModel_naturality.{u, v, w, r}]
  change ((SSet.uliftFunctor.{max u v w r, max u v}).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y)).inv ≫
      ((SSet.uliftFunctor.{max u v w r, max u v}).mapIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
