module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps

/-! # 実際の導来中間比較から通常のモデル計算射を回復する

## 概要
実際の導来中間比較から通常のモデル計算射を回復する。

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
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- source計算の逆とtarget計算で挟むと、既存の通常の解像度比較射を局所化した射になる。 -/
lemma derivedMiddleRestrictionComparison_calculation :
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) := by
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
