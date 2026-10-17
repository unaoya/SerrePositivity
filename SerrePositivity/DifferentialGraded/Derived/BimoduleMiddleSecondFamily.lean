module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeSecondFactor

/-! # 中間圏の標準導来比較の後因子自然性を自然変換の等式へ束ねる -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

def middleDerivedSourceFamilyMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedSourceFamily A B C D E F hE Q' :=
  whiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (whiskerLeft (bimoduleToDerived A B D)
      ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))))

def middleDerivedTargetFamilyMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedTargetFamily A B C E hE Q ⟶ middleDerivedTargetFamily A B C E hE Q' :=
  whiskerLeft (bimoduleToDerived A B C)
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom))

def derivedMiddleRestrictionCanonicalFamily (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedTargetFamily A B C E hE Q :=
  derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

lemma derivedMiddleRestrictionCanonicalFamily_app (Q : RightKFlatBimoduleCategory A C E)
    (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q).app P =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  derivedMiddleRestrictionComparisonFamily_app A B C D E F hE Q _ _ _ P

lemma derivedMiddleRestrictionCanonicalFamily_second_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceFamilyMap A B C D E F hE g ≫
        derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q' =
      derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q ≫
        middleDerivedTargetFamilyMap A B C E hE g := by
  apply NatTrans.ext
  funext P
  simp only [NatTrans.comp_app, derivedMiddleRestrictionCanonicalFamily_app]
  exact derivedMiddleRestrictionCanonicalComparison_second_naturality A B C D E F hE g P

/-- 後因子の射を、前因子の全導来圏上のsource関手族の間の自然変換へ降ろす。 -/
def middleDerivedSourceLiftMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLift A B C D E F hE Q ⟶ middleDerivedSourceLift A B C D E F hE Q' :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceFamily A B C D E F hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    (middleDerivedSourceFamilyMap A B C D E F hE g)

lemma middleDerivedTargetFamilyMap_lift {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedTargetFamily A B C E hE Q) (middleDerivedTargetFamily A B C E hE Q')
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
      (middleDerivedTargetFamilyMap A B C E hE g) =
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
      ((bimoduleToDerived A B C).obj P) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

lemma derivedMiddleRestrictionCanonicalFamily_lift (Q : RightKFlatBimoduleCategory A C E) :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedTargetFamily A B C E hE Q)
      (middleDerivedSourceLift A B C D E F hE Q)
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
      (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q) =
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := rfl

/-- 標準比較は、前因子の全導来圏上の自然変換としても後因子の射に自然。 -/
lemma derivedMiddleRestrictionCanonicalLocalized_second_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLiftMap A B C D E F hE g ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q' =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q ≫
        (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) := by
  have h := congrArg (fun τ => Localization.liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q') (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj)) τ)
    (derivedMiddleRestrictionCanonicalFamily_second_naturality A B C D E F hE g)
  have hleft := Localization.comp_liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedSourceFamily A B C D E F hE Q') (middleDerivedTargetFamily A B C E hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
    (middleDerivedSourceFamilyMap A B C D E F hE g)
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q')
  have hright := Localization.comp_liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q) (middleDerivedTargetFamily A B C E hE Q')
    (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q)
    (middleDerivedTargetFamilyMap A B C E hE g)
  rw [derivedMiddleRestrictionCanonicalFamily_lift] at hleft
  rw [derivedMiddleRestrictionCanonicalFamily_lift, middleDerivedTargetFamilyMap_lift] at hright
  exact hleft.trans (h.trans hright.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
