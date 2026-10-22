module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathModel

/-! 元の mapping cocone の空間模型を、同じ path 射影の実引き戻しに同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q)

lemma dgGluingCoconePathSpace_isPullback :
    IsPullback (complexPinchedMap.{u, v} (dgGluingCoconePathMap d))
      (complexPinchedMap.{u, v} (mappingCocone.fst d))
      (complexPinchedMap.{u, v} (mappingCocone.fst (𝟙 Q)))
      (complexPinchedMap.{u, v} d) :=
  dgGluingComplexPinchedMap_isPullback (dgGluingCoconePath_isPullback d)

def dgGluingCoconePathSpaceIso :
    complexPinchedSpace.{u, v} (mappingCocone d) ≅
      pullback (complexPinchedMap.{u, v} (mappingCocone.fst (𝟙 Q)))
        (complexPinchedMap.{u, v} d) :=
  (dgGluingCoconePathSpace_isPullback.{u, v} d).isoPullback

lemma dgGluingCoconePathSpaceIso_path :
    (dgGluingCoconePathSpaceIso.{u, v} d).hom ≫ pullback.fst _ _ =
      complexPinchedMap.{u, v} (dgGluingCoconePathMap d) :=
  (dgGluingCoconePathSpace_isPullback.{u, v} d).isoPullback_hom_fst

lemma dgGluingCoconePathSpaceIso_base :
    (dgGluingCoconePathSpaceIso.{u, v} d).hom ≫ pullback.snd _ _ =
      complexPinchedMap.{u, v} (mappingCocone.fst d) :=
  (dgGluingCoconePathSpace_isPullback.{u, v} d).isoPullback_hom_snd

variable (R) (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomComplex_pathSpace_isPullback (X Y : DGGluingObject R C D M) :
    IsPullback
      (complexPinchedMap.{u, max u v w}
        (dgGluingCoconePathMap (dgGluingDifference R C D M X Y)))
      (complexPinchedMap.{u, max u v w}
        (mappingCocone.fst (dgGluingDifference R C D M X Y)))
      (complexPinchedMap.{u, max u v w}
        (mappingCocone.fst (𝟙 (M.value X.left Y.right))))
      (complexPinchedMap.{u, max u v w} (dgGluingDifference R C D M X Y)) :=
  dgGluingCoconePathSpace_isPullback _

end SerrePositivity.InfinityCategories
