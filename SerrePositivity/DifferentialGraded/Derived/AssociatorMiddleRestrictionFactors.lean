module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionPresentation

/-! # 中間制限後の指定モデルと結合子比較に使う因子同型 -/
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
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D E hE
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj

/-- 既存の導来制限を、指定した制限後K-flatモデルの局所化像へ同定する。 -/
def middleRestrictionKFlatFactorIso :
    (derivedBimoduleRestriction A D E C E F (DGFunctor.id E)).obj QT ≅
      (bimoduleToDerived A D E).obj S.obj :=
  ((middleRightRestrictionDerivedIso A C D F E).app Q.obj).symm ≪≫
    (bimoduleDerivedIso A D E q hq).symm

/-- 因子同型の逆は、指定増大の局所化と既存制限表示を続けた射。 -/
lemma middleRestrictionKFlatFactorIso_inv :
    (middleRestrictionKFlatFactorIso A C D E F Q S q hq).inv =
      (bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj := rfl

/-- 中間比較のsource表示は、同じ因子同型と固定合成表示によるもの。 -/
lemma middleRestrictionKFlatSourceIso_hom :
    (middleRestrictionKFlatSourceIso A B C D E F hE Q S q hq).hom =
      whiskerLeft L
        ((HD).map (middleRestrictionKFlatFactorIso A C D E F Q S q hq).hom ≫
          (derivedBimoduleComposeKFlatIso A B D E hE S).hom) := by
  simp only [middleRestrictionKFlatSourceIso, middleRestrictionKFlatFactorIso,
    derivedBimoduleComposeResolutionComputation, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, whiskerLeft_comp, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
