module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleOutputRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleTransportComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleKFlatIndependence

/-! # 全導来中間比較を任意の指定モデルと出力制限で計算する

## 概要
全導来中間比較を任意の指定モデルと出力制限で計算する。

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- 中間比較のsource表示を、前因子・後因子の既存制限表示に分けた成分式。 -/
lemma middleDerivedSourceFamilyIdentification_hom_app_calc :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P =
      ((derivedBimoduleComposeFunctor A B D E hE).obj
        ((bimoduleToDerived A D E).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))).map
          ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      ((derivedBimoduleComposeFunctor A B D E hE).map
        ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)).app
          ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj
            ((bimoduleToDerived A B C).obj P)) := rfl

/-- 全導来中間比較のモデル計算は、制限後の任意の右相対K-flat解像度で行える。 -/
lemma derivedMiddleRestrictionNatTrans_resolution_calculation :
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
      ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) := by
  rw [← Category.assoc ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P),
    derivedMiddleRestrictionNatTrans_base_fac,
    ← derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D E F hE Q R q hq P]
  exact derivedMiddleRestrictionComparison_calculation A B C D E F hE P Q R q hq

variable (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)

local notation "S" => BimoduleCategory.of A B E
  (compose A B D E (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
    (BimoduleCategory.underlying A D E R.obj))
local notation "T" => BimoduleCategory.of A B E
  (compose A B C E (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj))
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- 全導来比較のモデル計算と、既存の出力側右制限表示の可換square。 -/
lemma derivedMiddleRestrictionNatTrans_resolution_output_restriction :
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫
      (RG).map
        ((middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
          (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
          ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
            ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app T := by
  have h := derivedMiddleRestrictionNatTrans_resolution_calculation A B C D E F hE P Q R q hq
  have hh := congrArg (fun k =>
    (middleRightRestrictionDerivedIso A B K G E).hom.app S ≫ (RG).map k) h
  exact hh.trans ((middleRightRestrictionDerivedIso A B K G E).hom.naturality
    (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
