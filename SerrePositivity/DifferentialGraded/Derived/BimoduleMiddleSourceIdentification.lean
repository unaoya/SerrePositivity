module
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComparison

/-! # 中間圏比較のsourceと既存の導来制限・導来合成の比較 -/
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

/-- 既存の導来制限と導来合成だけで表した中間圏比較のsource。 -/
def middleRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedBimoduleRestriction A D E C E F (DGFunctor.id E) ⋙
    derivedBimoduleComposeFunctor A B D E hE ⋙
      (whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B D B C (DGFunctor.id B) F)

/-- 閉零の後因子上で、前因子の局所化をまだ延長しないsource関手族。 -/
def middleClosedSourceFunctor : BimoduleCategory A C E ⥤
    (BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  (BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E) ⋙
    derivedBimoduleComposeFunctor A B D E hE ⋙
      (whiskeringLeft _ _ _).obj
        (BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D)

/-- 両因子の閉零射に自然な、既存の導来制限と導来合成へのsource表示比較。 -/
def middleClosedSourceIdentification :
    middleClosedSourceFunctor A B C D E F hE ≅
      bimoduleToDerived A C E ⋙ middleRestrictionDerivedSource A B C D E F hE ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B C) :=
  Functor.isoWhiskerLeft
      (BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E)
      (Functor.isoWhiskerLeft (derivedBimoduleComposeFunctor A B D E hE)
        ((whiskeringLeft _ _ _).mapIso (middleLeftRestrictionDerivedIso A B C D F))) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A C D F E)
      (derivedBimoduleComposeFunctor A B D E hE ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B C ⋙
          derivedBimoduleRestriction A B D B C (DGFunctor.id B) F))

/-- 閉零の前因子上で、既存のsourceを導来制限と導来合成へ比較する。 -/
def middleDerivedSourceFamilyIdentification (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamily A B C D E F hE Q ≅
      bimoduleToDerived A B C ⋙
        (middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj) :=
  (middleClosedSourceIdentification A B C D E F hE).app Q.obj

instance middleRestrictionSourceTarget_lifting (Q : RightKFlatBimoduleCategory A C E) :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)) := ⟨Iso.refl _⟩

/-- 指定右K-flat後因子について、前因子の全導来圏上のsourceを既存APIへ同定する。 -/
def middleDerivedSourceLiftIdentification (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceLift A B C D E F hE Q ≅
      (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q)
    (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (middleDerivedSourceLift A B C D E F hE Q)
    ((middleRestrictionDerivedSource A B C D E F hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q)

lemma middleRestrictionSourceTargetMap_lift
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q'.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q.obj))
      ((middleRestrictionDerivedSource A B C D E F hE).obj
        ((bimoduleToDerived A C E).obj Q'.obj))
      (whiskerLeft (bimoduleToDerived A B C)
        ((middleRestrictionDerivedSource A B C D E F hE).map
          ((bimoduleToDerived A C E).map g.hom))) =
      (middleRestrictionDerivedSource A B C D E F hE).map
        ((bimoduleToDerived A C E).map g.hom) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- sourceの同定は後因子の任意の閉零射に関しても自然。 -/
lemma middleDerivedSourceLiftIdentification_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLiftMap A B C D E F hE g ≫
        (middleDerivedSourceLiftIdentification A B C D E F hE Q').hom =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).hom ≫
        (middleRestrictionDerivedSource A B C D E F hE).map
          ((bimoduleToDerived A C E).map g.hom) := by
  rw [← middleRestrictionSourceTargetMap_lift A B C D E F hE g]
  unfold middleDerivedSourceLiftMap middleDerivedSourceLiftIdentification
  simp only [Localization.liftNatIso_hom, Localization.comp_liftNatTrans]
  congr 1
  exact (middleClosedSourceIdentification A B C D E F hE).hom.naturality g.hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
