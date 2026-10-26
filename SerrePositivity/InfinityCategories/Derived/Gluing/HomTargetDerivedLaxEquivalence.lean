module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUniverseIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxVertices
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：導来係数 lax 模型と元終域の二脚 lax 模型を、同じ元 gluing と左右射影の全関手同型を保って比較する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetNativeDerivedLaxEquivalence :=
  (qCatEquivalenceOfIso (dgGluingNativeUniverseIso (dgNerve R (DGGluingObject R C D M)))).trans
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M)

lemma dgGluingHomTargetNativeDerivedLaxEquivalence_fst :
    (dgGluingHomTargetNativeDerivedLaxEquivalence R C D E p q).hom ≫
      F2.laxPullbackFst
        (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) ≫
      (dgGluingNativeUniverseIso (dgNerve R C)).inv =
    dgNerve.map (dgGluingLeft R C D M) := by
  change ((dgGluingNativeUniverseIso (dgNerve R (DGGluingObject R C D M))).hom ≫
    dgGluingUniverseDerivedNerveLaxComparison R C D M) ≫ _ ≫ _ = _
  rw [Category.assoc, reassoc_of% dgGluingUniverseDerivedNerveLaxComparison_fst]
  exact dgGluingNativeUniverseNerveMap (dgGluingLeft R C D M)

lemma dgGluingHomTargetNativeDerivedLaxEquivalence_snd :
    (dgGluingHomTargetNativeDerivedLaxEquivalence R C D E p q).hom ≫
      F2.laxPullbackSnd
        (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) ≫
      (dgGluingNativeUniverseIso (dgNerve R D)).inv =
    dgNerve.map (dgGluingRight R C D M) := by
  change ((dgGluingNativeUniverseIso (dgNerve R (DGGluingObject R C D M))).hom ≫
    dgGluingUniverseDerivedNerveLaxComparison R C D M) ≫ _ ≫ _ = _
  rw [Category.assoc, reassoc_of% dgGluingUniverseDerivedNerveLaxComparison_snd]
  exact dgGluingNativeUniverseNerveMap (dgGluingRight R C D M)

def dgGluingHomTargetDerivedLaxEquivalence :
    QCatEquivalence
      (F2.laxPullback
        (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
      (F2.laxPullback (dgNerve.map p) (dgNerve.map q)) :=
  (dgGluingHomTargetNativeDerivedLaxEquivalence R C D E p q).symm.trans
    (dgGluingHomTargetNerveLaxEquivalence R C D E p q)

def dgGluingHomTargetDerivedLaxEquivalence_fst :
    FunctorIso
      ((dgGluingHomTargetDerivedLaxEquivalence R C D E p q).hom ≫
        F2.laxPullbackFst (dgNerve.map p) (dgNerve.map q))
      (F2.laxPullbackFst
        (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) ≫
          (dgGluingNativeUniverseIso (dgNerve R C)).inv) := by
  let e := dgGluingHomTargetNativeDerivedLaxEquivalence R C D E p q
  refine (eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f)) ?_)) ≪≫
    e.invHomIso.postcomp (F2.laxPullbackFst
      (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) ≫
        (dgGluingNativeUniverseIso (dgNerve R C)).inv)
  change (e.inv ≫ dgGluingHomTargetNerveLaxComparison R C D E p q) ≫ _ = _
  rw [Category.assoc, dgGluingHomTargetNerveLaxComparison_fst,
    ← dgGluingHomTargetNativeDerivedLaxEquivalence_fst R C D E p q]
  simp only [e, Category.assoc]

def dgGluingHomTargetDerivedLaxEquivalence_snd :
    FunctorIso
      ((dgGluingHomTargetDerivedLaxEquivalence R C D E p q).hom ≫
        F2.laxPullbackSnd (dgNerve.map p) (dgNerve.map q))
      (F2.laxPullbackSnd
        (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) ≫
          (dgGluingNativeUniverseIso (dgNerve R D)).inv) := by
  let e := dgGluingHomTargetNativeDerivedLaxEquivalence R C D E p q
  refine (eqToIso (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f)) ?_)) ≪≫
    e.invHomIso.postcomp (F2.laxPullbackSnd
      (dgGluingUniverseDerivedYoneda.{u, max (u + 1) v, max (u + 1) v} R C)
      (dgGluingUniverseDerivedCoefficient R C D M) ≫
        (dgGluingNativeUniverseIso (dgNerve R D)).inv)
  change (e.inv ≫ dgGluingHomTargetNerveLaxComparison R C D E p q) ≫ _ = _
  rw [Category.assoc, dgGluingHomTargetNerveLaxComparison_snd,
    ← dgGluingHomTargetNativeDerivedLaxEquivalence_snd R C D E p q]
  simp only [e, Category.assoc]

end SerrePositivity.InfinityCategories
