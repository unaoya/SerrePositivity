module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Projections

/-! 元の全 Hom 複体上の閉単位と合成、および元の二成分との厳密な両立。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の gluing Hom 複体上の実閉単位。 -/
def dgGluingIdentity (X : DGGluingObject R C D M) :
    𝟙_ (Complex R) ⟶ dgGluingHomComplex R C D M X X := eId (Complex R) X

/-- 元の全 Hom 複体上の実合成鎖写像。 -/
def dgGluingComposition (X Y Z : DGGluingObject R C D M) :
    dgGluingHomComplex R C D M X Y ⊗ dgGluingHomComplex R C D M Y Z ⟶
      dgGluingHomComplex R C D M X Z := eComp (Complex R) X Y Z

/-- 単位の左成分は元の左成分の閉単位。 -/
lemma dgGluingIdentity_left (X : DGGluingObject R C D M) :
    dgGluingIdentity R C D M X ≫ dgGluingLeftHomMap R C D M X X =
      eId (Complex R) X.left := dgGluingLeftHomMap_id R C D M X

/-- 単位の右成分も元の閉単位。 -/
lemma dgGluingIdentity_right (X : DGGluingObject R C D M) :
    dgGluingIdentity R C D M X ≫ dgGluingRightHomMap R C D M X X =
      eId (Complex R) X.right := by
  have h := (dgGluingRight R C D M).map_id X
  simpa only [dgGluingRight_map] using! h

/-- 合成の左成分は元の二射の豊穣合成。 -/
lemma dgGluingComposition_left (X Y Z : DGGluingObject R C D M) :
    dgGluingComposition R C D M X Y Z ≫ dgGluingLeftHomMap R C D M X Z =
      (dgGluingLeftHomMap R C D M X Y ⊗ₘ dgGluingLeftHomMap R C D M Y Z) ≫
        eComp (Complex R) X.left Y.left Z.left := dgGluingLeftHomMap_comp R C D M X Y Z

/-- 合成の右成分も元の二射の豊穣合成。 -/
lemma dgGluingComposition_right (X Y Z : DGGluingObject R C D M) :
    dgGluingComposition R C D M X Y Z ≫ dgGluingRightHomMap R C D M X Z =
      (dgGluingRightHomMap R C D M X Y ⊗ₘ dgGluingRightHomMap R C D M Y Z) ≫
        eComp (Complex R) X.right Y.right Z.right := by
  have h := (dgGluingRight R C D M).map_comp X Y Z
  simpa only [dgGluingRight_map] using! h

end SerrePositivity.InfinityCategories
