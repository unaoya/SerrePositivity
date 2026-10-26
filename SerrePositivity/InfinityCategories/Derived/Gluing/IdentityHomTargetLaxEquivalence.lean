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
variable (R : Type u) [CommRing R]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]

def dgGluingIdentityHomTargetLaxEquivalence :
    QCatEquivalence
      (dgNerve R (DGGluingObject R C C
        (dgHomGluingBimodule R C C C (DGFunctor.id C) (DGFunctor.id C))))
      (F2.laxPullback (𝟙 (dgNerve R C)) (𝟙 (dgNerve R C))) := by
  simpa only [dgNerve.map_id] using
    dgGluingHomTargetNerveLaxEquivalence.{u, v} R C C C (DGFunctor.id C) (DGFunctor.id C)

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
