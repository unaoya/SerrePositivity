module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomModelNaturality

/-! 実 Hom 作用を複体模型へ移すと、元の鎖写像の作用と宇宙変更だけが残る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] {x y : C} {x' y' : D}

def dgGluingUniverseHomModelComparison
    (φ : homObject R C x y ⟶ homObject R D x' y') :
    (SSet.uliftFunctor.{max u v w r, max u v}).obj
        (complexPinchedSpace.{u, v} (homObject R C x y)) ⟶
      (SSet.uliftFunctor.{max u v w r, max u w}).obj
        (complexPinchedSpace.{u, w} (homObject R D x' y')) :=
  (SSet.uliftFunctor.{max u v w r, max u v}).map (pinchedComplexModelIso x y).inv ≫
    dgGluingUniverseHomChainMap.{u, v, w, max u v w r} φ ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map (pinchedComplexModelIso x' y').hom

lemma dgGluingUniverseHomModelComparison_eq
    (φ : homObject R C x y ⟶ homObject R D x' y') :
    dgGluingUniverseHomModelComparison.{u, v, w, r} φ =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} (homObject R D x' y')).hom := by
  rw [dgGluingUniverseHomModelComparison, dgGluingUniverseHomModel_naturality.{u, v, w, r}]
  change ((SSet.uliftFunctor.{max u v w r, max u v}).mapIso
    (pinchedComplexModelIso x y)).inv ≫
      ((SSet.uliftFunctor.{max u v w r, max u v}).mapIso
        (pinchedComplexModelIso x y)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
