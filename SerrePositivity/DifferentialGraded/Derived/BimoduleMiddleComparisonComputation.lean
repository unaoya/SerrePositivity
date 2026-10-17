module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceFull

/-! # 全導来中間比較を指定K-flatモデルで計算する入口 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma replacementConjugate_precomp
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (E : C ⥤ D) (hE : E.FullyFaithful) (R : D ⥤ C) (ε : R ⋙ E ≅ 𝟭 D)
    (U H : D ⥤ T) (τ : E ⋙ U ⟶ E ⋙ H) (X : C) :
    U.map (ε.app (E.obj X)).inv ≫ τ.app (R.obj (E.obj X)) ≫
        H.map (ε.app (E.obj X)).hom = τ.app X := by
  let f : R.obj (E.obj X) ⟶ X := hE.preimage (ε.app (E.obj X)).hom
  have hf : E.map f = (ε.app (E.obj X)).hom := hE.map_preimage _
  have hn := τ.naturality f
  change U.map (E.map f) ≫ τ.app X = τ.app (R.obj (E.obj X)) ≫ H.map (E.map f) at hn
  rw [hf] at hn
  rw [← hn, ← Category.assoc, ← U.map_comp, Iso.inv_hom_id, U.map_id, Category.id_comp]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 右K-flat局所化上で、sourceを既存の導来制限表示へ移した実際の比較。 -/
def middleLocalizedRestrictionComparison :
    rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE ⟶
      rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE :=
  (middleRightKFlatSourceIdentification A B C D E F hE).inv ≫
    middleRightKFlatLocalizedComparison A B C D E F hE

/-- 全導来比較は、指定置換の余単位で局所化上の比較を移したものである。 -/
lemma derivedMiddleRestrictionNatTrans_conjugate (Q : DerivedBimoduleCategory A C E) :
    (derivedMiddleRestrictionNatTrans A B C D E F hE).app Q =
      (middleRestrictionDerivedSource A B C D E F hE).map
          ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
        (middleLocalizedRestrictionComparison A B C D E F hE).app
          ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
        (derivedBimoduleComposeFunctor A B C E hE).map
          ((rightKFlatReplacementCounitIso A C E hE).app Q).hom := by
  dsimp only [derivedMiddleRestrictionNatTrans, middleFullDerivedSourceIdentification,
    middleFullDerivedComparison, middleFullDerivedTargetIso, middleLocalizedRestrictionComparison,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  exact congrArg (fun f => (middleRestrictionDerivedSource A B C D E F hE).map
    ((rightKFlatReplacementCounitIso A C E hE).app Q).inv ≫
    (middleRightKFlatSourceIdentification A B C D E F hE).inv.app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
    (middleRightKFlatLocalizedComparison A B C D E F hE).app
      ((derivedRightKFlatReplacement A C E hE).obj Q) ≫ f)
    (Category.comp_id ((derivedBimoduleComposeFunctor A B C E hE).map
      ((rightKFlatReplacementCounitIso A C E hE).app Q).hom))

/-- 右K-flat局所化への制限は、元の局所化上の比較を厳密に回復する。 -/
lemma derivedMiddleRestrictionNatTrans_precomp_rightKFlat :
    whiskerLeft (rightKFlatDerivedInclusion A C E)
        (derivedMiddleRestrictionNatTrans A B C D E F hE) =
      middleLocalizedRestrictionComparison A B C D E F hE := by
  apply NatTrans.ext
  funext Q
  rw [whiskerLeft_app, derivedMiddleRestrictionNatTrans_conjugate]
  exact replacementConjugate_precomp (rightKFlatDerivedInclusion A C E)
    (rightKFlatDerivedInclusion_fullyFaithful A C E hE) (derivedRightKFlatReplacement A C E hE)
    (rightKFlatReplacementCounitIso A C E hE)
    (middleRestrictionDerivedSource A B C D E F hE)
    (derivedBimoduleComposeFunctor A B C E hE)
    (middleLocalizedRestrictionComparison A B C D E F hE) Q

lemma middleLocalizedRestrictionComparison_eq_lift :
    middleLocalizedRestrictionComparison A B C D E F hE =
      Localization.liftNatTrans (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
          middleRestrictionDerivedSource A B C D E F hE)
        (middleDerivedTargetKFlatFunctor A B C E hE)
        (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE)
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
        ((middleSourceKFlatIdentification A B C D E F hE).inv ≫
          middleDerivedKFlatComparison A B C D E F hE) := by
  unfold middleLocalizedRestrictionComparison middleRightKFlatSourceIdentification
    middleRightKFlatLocalizedComparison
  simp only [Localization.liftNatIso_inv, Localization.comp_liftNatTrans]

lemma middleLocalizedRestrictionComparison_app (Q : RightKFlatBimoduleCategory A C E) :
    (middleLocalizedRestrictionComparison A B C D E F hE).app
        ((rightKFlatToDerived A C E).obj Q) =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := by
  rw [middleLocalizedRestrictionComparison_eq_lift, Localization.liftNatTrans_app]
  change 𝟙 _ ≫ ((middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
    derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- 全導来比較を、指定された任意の右K-flat後因子上で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app_rightKFlat (Q : RightKFlatBimoduleCategory A C E) :
    (derivedMiddleRestrictionNatTrans A B C D E F hE).app ((bimoduleToDerived A C E).obj Q.obj) =
      (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := by
  have h := NatTrans.congr_app (derivedMiddleRestrictionNatTrans_precomp_rightKFlat
    A B C D E F hE) ((rightKFlatToDerived A C E).obj Q)
  exact h.trans (middleLocalizedRestrictionComparison_app A B C D E F hE Q)

lemma middleRightKFlatComparison_eq_first_lift (Q : RightKFlatBimoduleCategory A C E) :
    (middleDerivedSourceLiftIdentification A B C D E F hE Q).inv ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q =
      Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (bimoduleToDerived A B C ⋙ (middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))
        (middleDerivedTargetFamily A B C E hE Q)
        ((middleRestrictionDerivedSource A B C D E F hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
        ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv ≫
          derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q) := by
  rw [← derivedMiddleRestrictionCanonicalFamily_lift]
  unfold middleDerivedSourceLiftIdentification
  simp only [Localization.liftNatIso_inv, Localization.comp_liftNatTrans]

/-- 既存の全導来制限表示における比較を、元の閉零前因子と右K-flat後因子で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app_base (Q : RightKFlatBimoduleCategory A C E)
    (P : BimoduleCategory A B C) :
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) =
      (middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv.app P ≫
        derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  have h := NatTrans.congr_app
    (derivedMiddleRestrictionNatTrans_app_rightKFlat A B C D E F hE Q)
    ((bimoduleToDerived A B C).obj P)
  refine h.trans ?_
  have h' := NatTrans.congr_app
    (middleRightKFlatComparison_eq_first_lift A B C D E F hE Q)
    ((bimoduleToDerived A B C).obj P)
  refine h'.trans ?_
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, middleRestrictionSourceTarget_lifting,
    middleDerivedTargetFamily_lifting, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [Category.id_comp]
  simp only [NatTrans.comp_app, derivedMiddleRestrictionCanonicalFamily_app]
  exact Category.comp_id
    ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).inv.app P ≫
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q)

end SerrePositivity.DifferentialGraded.BimoduleTensor
