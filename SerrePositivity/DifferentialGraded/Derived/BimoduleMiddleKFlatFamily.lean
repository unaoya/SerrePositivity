module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSecondFamily

/-! # 中間圏比較のsource関手族と右K-flat後因子の準同型局所化への準備 -/
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

lemma middleDerivedSourceFamilyMap_id (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamilyMap A B C D E F hE (𝟙 Q) = 𝟙 _ := by
  change whiskerLeft _ (whiskerLeft _ ((derivedBimoduleComposeFunctor A B D E hE).map
    ((bimoduleToDerived A D E).map
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map (𝟙 Q.obj))))) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma middleDerivedSourceFamilyMap_comp {Q Q' Q'' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') (k : Q' ⟶ Q'') :
    middleDerivedSourceFamilyMap A B C D E F hE (g ≫ k) =
      middleDerivedSourceFamilyMap A B C D E F hE g ≫
        middleDerivedSourceFamilyMap A B C D E F hE k := by
  change whiskerLeft _ (whiskerLeft _ ((derivedBimoduleComposeFunctor A B D E hE).map
    ((bimoduleToDerived A D E).map
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map (g.hom ≫ k.hom))))) = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, whiskerLeft_comp, whiskerLeft_comp]
  rfl

lemma middleDerivedSourceLiftMap_id (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceLiftMap A B C D E F hE (𝟙 Q) = 𝟙 _ := by
  unfold middleDerivedSourceLiftMap
  rw [middleDerivedSourceFamilyMap_id]
  exact Localization.liftNatTrans_id _ _ _ _

lemma middleDerivedSourceLiftMap_comp {Q Q' Q'' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') (k : Q' ⟶ Q'') :
    middleDerivedSourceLiftMap A B C D E F hE (g ≫ k) =
      middleDerivedSourceLiftMap A B C D E F hE g ≫
        middleDerivedSourceLiftMap A B C D E F hE k := by
  unfold middleDerivedSourceLiftMap
  rw [middleDerivedSourceFamilyMap_comp, Localization.comp_liftNatTrans]

/-- 後因子の右K-flat部分圏上で、前因子の全導来圏の関手へ値を取るsource関手族。 -/
def middleDerivedSourceKFlatFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) where
  obj Q := middleDerivedSourceLift A B C D E F hE Q
  map g := middleDerivedSourceLiftMap A B C D E F hE g
  map_id := middleDerivedSourceLiftMap_id A B C D E F hE
  map_comp := middleDerivedSourceLiftMap_comp A B C D E F hE

def middleDerivedTargetKFlatFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ derivedBimoduleComposeFunctor A B C E hE

/-- 標準比較を右K-flat後因子の圏上の自然変換として束ねる。 -/
def middleDerivedKFlatComparison :
    middleDerivedSourceKFlatFunctor A B C D E F hE ⟶
      middleDerivedTargetKFlatFunctor A B C E hE where
  app Q := derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q
  naturality {_Q _Q'} g :=
    derivedMiddleRestrictionCanonicalLocalized_second_naturality A B C D E F hE g

lemma middleDerivedSourceKFlatFunctor_inverts :
    (rightKFlatQuasiIso A C E).IsInvertedBy (middleDerivedSourceKFlatFunctor A B C D E F hE) := by
  intro Q Q' g hg
  let f := BimoduleCategory.middleRightRestrictionMap A C D E F g.hom
  have hf : BimoduleCategory.quasiIso A D E f := by
    intro d e
    rw [BimoduleCategory.middleRightRestrictionMap_value_eval]
    exact hg (F.obj d) e
  let e := Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (Functor.isoWhiskerLeft (bimoduleToDerived A B D)
      ((derivedBimoduleComposeFunctor A B D E hE).mapIso (bimoduleDerivedIso A D E f hf)))
  have : IsIso (middleDerivedSourceFamilyMap A B C D E F hE g) := e.isIso_hom
  exact (Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceFamily A B C D E F hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    (asIso (middleDerivedSourceFamilyMap A B C D E F hE g))).isIso_hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
