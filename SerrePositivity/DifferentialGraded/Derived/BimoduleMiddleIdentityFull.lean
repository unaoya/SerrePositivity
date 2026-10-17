module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentityFamily

/-! # 恒等中間比較と左右制限のsource正規化の全導来関手族上での一致 -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 左右の恒等制限から作る正規化同型は、右K-flat後因子の任意の閉零射にも自然。 -/
def middleIdentityKFlatIso :
    middleDerivedSourceKFlatFunctor A B D D L (DGFunctor.id D) hL ≅
      middleDerivedTargetKFlatFunctor A B D L hL :=
  NatIso.ofComponents (middleIdentitySourceLiftIso A B D L hL) (by
    intro Q Q' g
    change middleDerivedSourceLiftMap A B D D L (DGFunctor.id D) hL g ≫
        (middleIdentitySourceLiftIso A B D L hL Q').hom =
      (middleIdentitySourceLiftIso A B D L hL Q).hom ≫
        (derivedBimoduleComposeFunctor A B D L hL).map ((bimoduleToDerived A D L).map g.hom)
    rw [← derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q',
      ← derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q]
    exact derivedMiddleRestrictionCanonicalLocalized_second_naturality
      A B D D L (DGFunctor.id D) hL g)

lemma middleDerivedKFlatComparison_functor_id :
    middleDerivedKFlatComparison A B D D L (DGFunctor.id D) hL =
      (middleIdentityKFlatIso A B D L hL).hom := by
  apply NatTrans.ext
  funext Q
  exact derivedMiddleRestrictionCanonicalLocalized_functor_id A B D L hL Q

/-- 指定右K-flat局所化上のsource正規化同型。 -/
def middleIdentityLocalizedIso :
    middleRightKFlatLocalizedSource A B D D L (DGFunctor.id D) hL ≅
      rightKFlatDerivedInclusion A D L ⋙ derivedBimoduleComposeFunctor A B D L hL :=
  Localization.liftNatIso (rightKFlatToDerived A D L) (rightKFlatQuasiIso A D L)
    (middleDerivedSourceKFlatFunctor A B D D L (DGFunctor.id D) hL)
    (middleDerivedTargetKFlatFunctor A B D L hL)
    (middleRightKFlatLocalizedSource A B D D L (DGFunctor.id D) hL)
    (rightKFlatDerivedInclusion A D L ⋙ derivedBimoduleComposeFunctor A B D L hL)
    (middleIdentityKFlatIso A B D L hL)

lemma middleRightKFlatLocalizedComparison_functor_id :
    middleRightKFlatLocalizedComparison A B D D L (DGFunctor.id D) hL =
      (middleIdentityLocalizedIso A B D L hL).hom := by
  unfold middleRightKFlatLocalizedComparison middleIdentityLocalizedIso
  rw [middleDerivedKFlatComparison_functor_id]
  rfl

/-- 両変数の全導来圏上のsource正規化。実際の比較射の可逆性から定義していない。 -/
def middleFullIdentityIso :
    middleFullDerivedSource A B D D L (DGFunctor.id D) hL ≅
      derivedBimoduleComposeFunctor A B D L hL :=
  Functor.isoWhiskerLeft (derivedRightKFlatReplacement A D L hL)
    (middleIdentityLocalizedIso A B D L hL) ≪≫ middleFullDerivedTargetIso A B D L hL

lemma middleFullDerivedComparison_functor_id :
    middleFullDerivedComparison A B D D L (DGFunctor.id D) hL =
      (middleFullIdentityIso A B D L hL).hom := by
  unfold middleFullDerivedComparison middleFullIdentityIso
  rw [middleRightKFlatLocalizedComparison_functor_id]
  rfl

/-- 既存の導来制限・導来合成で表したsourceを正規化する、両変数の全導来自然同型。 -/
def derivedMiddleIdentityIso :
    middleRestrictionDerivedSource A B D D L (DGFunctor.id D) hL ≅
      derivedBimoduleComposeFunctor A B D L hL :=
  (middleFullDerivedSourceIdentification A B D D L (DGFunctor.id D) hL).symm ≪≫
    middleFullIdentityIso A B D L hL

/-- 既存の実際の全導来比較は、左右制限の恒等同型から構成した正規化に一致する。 -/
lemma derivedMiddleRestrictionNatTrans_functor_id :
    derivedMiddleRestrictionNatTrans A B D D L (DGFunctor.id D) hL =
      (derivedMiddleIdentityIso A B D L hL).hom := by
  unfold derivedMiddleRestrictionNatTrans derivedMiddleIdentityIso
  rw [middleFullDerivedComparison_functor_id]
  rfl

lemma derivedMiddleIdentityIso_transport :
    (middleFullDerivedSourceIdentification A B D D L (DGFunctor.id D) hL).hom ≫
        (derivedMiddleIdentityIso A B D L hL).hom = (middleFullIdentityIso A B D L hL).hom := by
  unfold derivedMiddleIdentityIso
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
