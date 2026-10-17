module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeIndependence

/-! # 全導来中間比較の表示移送付きモデル計算

## 概要
全導来中間比較の表示移送付きモデル計算。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- source表示同型を前合成すると、元の標準モデル計算を回復する。 -/
lemma derivedMiddleRestrictionNatTrans_base_fac
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
        ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
          ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  rw [derivedMiddleRestrictionNatTrans_app_base, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp]

/-- 任意の導来射で両因子を移送した全導来比較を、指定右K-flatモデルで計算する。 -/
lemma derivedMiddleRestrictionNatTrans_transport_fac
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C)
    (Q' : DerivedBimoduleCategory A C E) (P' : DerivedBimoduleCategory A B C)
    (g : (bimoduleToDerived A C E).obj Q.obj ⟶ Q')
    (f : (bimoduleToDerived A B C).obj P ⟶ P') :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
        ((middleRestrictionDerivedSource A B C D E F hE).map g).app
          ((bimoduleToDerived A B C).obj P) ≫
        ((middleRestrictionDerivedSource A B C D E F hE).obj Q').map f ≫
        ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q').app P' =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q ≫
        ((derivedBimoduleComposeFunctor A B C E hE).map g).app
          ((bimoduleToDerived A B C).obj P) ≫
        ((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f := by
  have hQ := NatTrans.congr_app
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).naturality g)
    ((bimoduleToDerived A B C).obj P)
  have hP := ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q').naturality f
  simp only [NatTrans.comp_app] at hQ
  rw [hP, ← Category.assoc _ _
    (((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f), hQ]
  simpa only [Category.assoc] using congrArg (fun k => k ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map g).app
      ((bimoduleToDerived A B C).obj P) ≫
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q').map f)
    (derivedMiddleRestrictionNatTrans_base_fac A B C D E F hE Q P)

end SerrePositivity.DifferentialGraded.BimoduleTensor
