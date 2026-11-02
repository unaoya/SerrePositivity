module
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso
public import SerrePositivity.DifferentialGraded.Bimodule.Value


/-! # 既存の導来bimodule制限の二段階合成の正規化

## 概要
既存の導来bimodule制限の二段階合成の正規化。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 元の対象に前合成した導来左制限の合成比較。直接制限の合成同型から構成する。 -/
def middleLeftDerivedCompPreIso :
    bimoduleToDerived A B T ⋙
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) ≅
      bimoduleToDerived A B T ⋙
        derivedBimoduleRestriction A B D B T (DGFunctor.id B) (F.comp G) :=
  Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B T E G).symm
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B T E G)
      (middleLeftRestrictionDerivedIso A B E D F).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G)
      (bimoduleToDerived A B D) ≪≫
    middleLeftRestrictionDerivedIso A B T D (F.comp G)

/-- 左制限の合成比較を全導来圏上の自然同型へ降ろす。 -/
def middleLeftDerivedCompIso :
    derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F ≅
      derivedBimoduleRestriction A B D B T (DGFunctor.id B) (F.comp G) :=
  bimoduleDerivedIsoOfPrecomp A B T _ _ (middleLeftDerivedCompPreIso A B D E T F G)

lemma middleLeftDerivedCompIso_hom_app (P : BimoduleCategory A B T) :
    (middleLeftDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A B T).obj P) =
      (middleLeftDerivedCompPreIso A B D E T F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B T _ _ _ P

/-- 元の対象に前合成した導来右制限の合成比較。 -/
def middleRightDerivedCompPreIso :
    bimoduleToDerived A T B ⋙
        (derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
          derivedBimoduleRestriction A D B E B F (DGFunctor.id B)) ≅
      bimoduleToDerived A T B ⋙
        derivedBimoduleRestriction A D B T B (F.comp G) (DGFunctor.id B) :=
  Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A T E G B).symm
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A T E B G)
      (middleRightRestrictionDerivedIso A E D F B).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.middleRightRestrictionCompIso A D B E T F G)
      (bimoduleToDerived A D B) ≪≫
    middleRightRestrictionDerivedIso A T D (F.comp G) B

/-- 右制限の合成比較を全導来圏上の自然同型へ降ろす。 -/
def middleRightDerivedCompIso :
    derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
        derivedBimoduleRestriction A D B E B F (DGFunctor.id B) ≅
      derivedBimoduleRestriction A D B T B (F.comp G) (DGFunctor.id B) :=
  bimoduleDerivedIsoOfPrecomp A T B _ _ (middleRightDerivedCompPreIso A B D E T F G)

lemma middleRightDerivedCompIso_hom_app (Q : BimoduleCategory A T B) :
    (middleRightDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A T B).obj Q) =
      (middleRightDerivedCompPreIso A B D E T F G).hom.app Q :=
  bimoduleDerivedIsoOfPrecomp_hom_app A T B _ _ _ Q

/-- 左制限の合成比較は、直接制限との表示同型に関して可換である。 -/
lemma middleLeftDerivedCompIso_presentation (P : BimoduleCategory A B T) :
    (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        ((middleLeftRestrictionDerivedIso A B T E G).hom.app P) ≫
      (middleLeftDerivedCompIso A B D E T F G).hom.app
        ((bimoduleToDerived A B T).obj P) =
    (bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionCompObjIso A B D E T F G P).hom ≫
      (middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom.app P := by
  rw [middleLeftDerivedCompIso_hom_app]
  simp only [middleLeftDerivedCompPreIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app, whiskerRight_app]
  rw [← (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rfl

/-- 右制限の合成比較も、直接制限との表示同型に関して可換である。 -/
lemma middleRightDerivedCompIso_presentation (Q : BimoduleCategory A T B) :
    (middleRightRestrictionDerivedIso A E D F B).hom.app
        ((BimoduleCategory.middleRightRestrictionFunctor A T E B G).obj Q) ≫
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)).map
        ((middleRightRestrictionDerivedIso A T E G B).hom.app Q) ≫
      (middleRightDerivedCompIso A B D E T F G).hom.app
        ((bimoduleToDerived A T B).obj Q) =
    (bimoduleToDerived A D B).map
        (BimoduleCategory.middleRightRestrictionCompObjIso A D B E T F G Q).hom ≫
      (middleRightRestrictionDerivedIso A T D (F.comp G) B).hom.app Q := by
  rw [middleRightDerivedCompIso_hom_app]
  simp only [middleRightDerivedCompPreIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app, whiskerRight_app]
  rw [← (derivedBimoduleRestriction A D B E B F (DGFunctor.id B)).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rfl

/-- 元の対象への前合成では、導来合成同型は構成に使った比較を回復する。 -/
lemma middleLeftDerivedCompIso_precomp :
    whiskerLeft (bimoduleToDerived A B T) (middleLeftDerivedCompIso A B D E T F G).hom =
      (middleLeftDerivedCompPreIso A B D E T F G).hom := by
  apply NatTrans.ext
  funext P
  exact middleLeftDerivedCompIso_hom_app A B D E T F G P

lemma middleRightDerivedCompIso_precomp :
    whiskerLeft (bimoduleToDerived A T B) (middleRightDerivedCompIso A B D E T F G).hom =
      (middleRightDerivedCompPreIso A B D E T F G).hom := by
  apply NatTrans.ext
  funext Q
  exact middleRightDerivedCompIso_hom_app A B D E T F G Q

end SerrePositivity.DifferentialGraded
