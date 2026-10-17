module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleNaturality
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition

/-! # 制限後の指定K-flatモデルを用いる導来中間比較 -/
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
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (Q : RightKFlatBimoduleCategory A C E) (S : RightKFlatBimoduleCategory A D E)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "KS" => rightKFlatDerivedCompose A B D E S
local notation "KQ" => rightKFlatDerivedCompose A B C E Q

/-- 固定モデルで合成するsourceの、前因子の局所化前での表示。 -/
def rightKFlatMiddleSourceBaseIso :
    bimoduleToDerived A B C ⋙ (L ⋙ KS) ≅
      BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙
        composeWith A B D E S.obj ⋙ bimoduleToDerived A B E :=
  Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B C D F).symm KS ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
      (eqToIso (derivedComposeWith_fac A B D E S.obj S.property))

/-- 通常の指定増大による比較を前因子の局所化へ延長する前の自然変換。 -/
def rightKFlatMiddlePreComparison :
    bimoduleToDerived A B C ⋙ (L ⋙ KS) ⟶ bimoduleToDerived A B C ⋙ KQ :=
  (rightKFlatMiddleSourceBaseIso A B C D E F S).hom ≫
    whiskerRight (middleRestrictionResolvedNatTrans A B C D E F Q.obj S.obj q)
      (bimoduleToDerived A B E) ≫
    (eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)).inv

/-- 制限後のK-flat性を仮定せず、指定K-flatモデルの任意の増大を用いる導来比較。 -/
def rightKFlatMiddleComparison : L ⋙ KS ⟶ KQ := by
  letI sourceLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ (L ⋙ KS)) (L ⋙ KS) :=
    ⟨Iso.refl _⟩
  letI targetLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ KQ) KQ := ⟨Iso.refl _⟩
  exact Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ (L ⋙ KS)) (bimoduleToDerived A B C ⋙ KQ)
    (L ⋙ KS) KQ (rightKFlatMiddlePreComparison A B C D E F Q S q)

/-- 元の前因子上で、入力制限表示の逆と通常の指定増大の比較へ計算する。 -/
lemma rightKFlatMiddleComparison_base_app (P : BimoduleCategory A B C) :
    (rightKFlatMiddleComparison A B C D E F Q S q).app ((bimoduleToDerived A B C).obj P) =
    (KS).map ((middleLeftRestrictionDerivedIso A B C D F).inv.app P) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj q) := by
  unfold rightKFlatMiddleComparison
  rw [Localization.liftNatTrans_app]
  simp only [rightKFlatMiddlePreComparison, rightKFlatMiddleSourceBaseIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  change 𝟙 _ ≫ ((_ ≫ 𝟙 _) ≫ _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- 入力制限表示を前置すると、局所化した通常の比較を回復する。 -/
lemma rightKFlatMiddleComparison_base_square (P : BimoduleCategory A B C) :
    (KS).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightKFlatMiddleComparison A B C D E F Q S q).app ((bimoduleToDerived A B C).obj P) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj q) := by
  rw [rightKFlatMiddleComparison_base_app, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
