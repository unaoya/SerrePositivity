module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxEquivalence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCospanIsoEquivalence
/-!
概要：恒等 Hom gluing の全 lax 比較と、恒等二脚の指定基底同値による輸送。
方針：元終域比較を恒等関手へ特殊化し、同じ三成分同値を使う。
規約：実逆を持つ全圏同値。対角・cone の比較は別工程。
使われ方：恒等二脚の固定入力比較の中央同値。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]

def dgGluingIdentityHomTargetLaxComparison :
    dgNerve R (DGGluingObject R C C
      (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))) ⟶
      F2.laxPullback (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C)) :=
  F2.laxPullbackLift _ _
    (dgNerve.map (dgGluingLeft R C C
      (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))))
    (dgNerve.map (dgGluingRight R C C
      (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))))
    (dgGluingHomTargetAugmentationArrowFamily R C C C (DGFunctor.id C) (DGFunctor.id C))
    (by
      simpa only [dgNerve.map_id (A := R) (D := C), Category.comp_id] using
        (dgGluingHomTargetAugmentationArrowFamily_source.{u, v} R C C C
          (DGFunctor.id C) (DGFunctor.id C)))
    (by
      simpa only [dgNerve.map_id (A := R) (D := C), Category.comp_id] using
        (dgGluingHomTargetAugmentationArrowFamily_target.{u, v} R C C C
          (DGFunctor.id C) (DGFunctor.id C)))

lemma dgGluingIdentityHomTargetLaxComparison_isQCatEquivalence :
    IsQCatEquivalence (dgGluingIdentityHomTargetLaxComparison.{u, v} R C) := by
  let l := dgNerve.map (dgGluingLeft R C C
    (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C)))
  let r := dgNerve.map (dgGluingRight R C C
    (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C)))
  let a := dgGluingHomTargetAugmentationArrowFamily R C C C (DGFunctor.id C) (DGFunctor.id C)
  have transport (j : dgNerve R C ⟶ dgNerve R C) (hj : j = 𝟙 _)
      (hs : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = l ≫ j)
      (ht : a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = r ≫ j)
      (he : IsQCatEquivalence (F2.laxPullbackLift j j l r a hs ht)) :
      IsQCatEquivalence (dgGluingIdentityHomTargetLaxComparison.{u, v} R C) := by
    subst j
    exact he
  exact transport (dgNerve.map (DGFunctor.id C)) (dgNerve.map_id (A := R) (D := C))
    (dgGluingHomTargetAugmentationArrowFamily_source.{u, v} R C C C
      (DGFunctor.id C) (DGFunctor.id C))
    (dgGluingHomTargetAugmentationArrowFamily_target.{u, v} R C C C
      (DGFunctor.id C) (DGFunctor.id C))
    (dgGluingHomTargetNerveLaxComparison_isQCatEquivalence.{u, v} R C C C
      (DGFunctor.id C) (DGFunctor.id C))

def dgGluingIdentityHomTargetLaxEquivalence :
    QCatEquivalence
      (dgNerve R (DGGluingObject R C C
        (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))))
      (F2.laxPullback (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))) :=
  (dgGluingIdentityHomTargetLaxComparison_isQCatEquivalence.{u, v} R C).choose

def identityLaxChangeBaseEquivalence {X Y : SSet.{v}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    QCatEquivalence (F2.laxPullback (𝟙 X) (𝟙 X))
      (F2.laxPullback (𝟙 Y) (𝟙 Y)) :=
  F2.laxPullbackCospanIsoEquivalence (𝟙 X) (𝟙 X) (𝟙 Y) (𝟙 Y)
    e.hom e.hom e.hom
    (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
      ((Category.id_comp e.hom).trans (Category.comp_id e.hom).symm)))
    (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
      ((Category.id_comp e.hom).trans (Category.comp_id e.hom).symm)))
    e.isQCatEquivalence e.isQCatEquivalence e.isQCatEquivalence

end SerrePositivity.InfinityCategories
