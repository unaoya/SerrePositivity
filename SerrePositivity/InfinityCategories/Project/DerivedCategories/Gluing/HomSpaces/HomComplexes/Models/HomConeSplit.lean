module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeBiproduct
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeExplicit

/-! 元の gluing Hom cone の左右成分を、実射影・実包含を保って分離する。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

/-- 閉左成分による、元の左 Hom の実後合成。 -/
def dgGluingHomConeLeftArrow : homObject R C X.left Y.left ⟶ homObject R C X.left Z.left :=
  eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.left)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map f)

/-- 閉右成分による、元の右 Hom の実後合成。 -/
def dgGluingHomConeRightArrow :
    homObject R D X.right Y.right ⟶ homObject R D X.right Z.right :=
  eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.right)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)

lemma dgGluingPostcompositionComponents_eq_biprod :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f =
      biprod.map (dgGluingHomConeLeftArrow R C D M X Y Z f)
        (dgGluingHomConeRightArrow R C D M X Y Z f) := by
  apply biprod.hom_ext <;>
    simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents, dgGluingHomConeLeftArrow,
      dgGluingHomConeRightArrow]

/-- 元の成分写像と対角直和写像の等式による cone の同型。 -/
def dgGluingHomConeDiagonalIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f) ≅
      mappingCone (biprod.map (dgGluingHomConeLeftArrow R C D M X Y Z f)
        (dgGluingHomConeRightArrow R C D M X Y Z f)) :=
  eqToIso (congrArg (fun a :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ⟶
    (homObject R C X.left Z.left ⊞ homObject R D X.right Z.right) => mappingCone a)
      (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f))

/-- 同じ左右成分の Hom cone の直和分解。 -/
def dgGluingHomConeBiproductIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f) ≅
      mappingCone (dgGluingHomConeLeftArrow R C D M X Y Z f) ⊞
        mappingCone (dgGluingHomConeRightArrow R C D M X Y Z f) :=
  dgGluingHomConeDiagonalIso R C D M X Y Z f ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso (dgGluingHomConeLeftArrow R C D M X Y Z f)
      (dgGluingHomConeRightArrow R C D M X Y Z f)

/-- 分解後も元の作用と第三成分を使う同じ実係数。 -/
def dgGluingHomConeSplitCoefficient :
    (mappingCone (dgGluingHomConeLeftArrow R C D M X Y Z f) ⊞
      mappingCone (dgGluingHomConeRightArrow R C D M X Y Z f)) ⟶
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f) :=
  (dgGluingHomConeBiproductIso R C D M X Y Z f).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitCoefficient R C D M X Y Z f

/-- 元の実 Hom 後合成の cone を、左右の Hom cone を分離した係数へ移す。 -/
def dgGluingHomConeSplitIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≅
      mappingCocone (dgGluingHomConeSplitCoefficient R C D M X Y Z f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso R C D M X Y Z f ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitCoefficient R C D M X Y Z f)
      (dgGluingHomConeSplitCoefficient R C D M X Y Z f)
      (dgGluingHomConeBiproductIso R C D M X Y Z f) (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id, dgGluingHomConeSplitCoefficient,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp])

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
