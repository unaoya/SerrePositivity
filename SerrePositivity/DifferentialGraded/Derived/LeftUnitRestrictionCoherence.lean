module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionTransport
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatIsoLiftComputation

/-! # 全導来左単位経路と制限後の既存左単位子の一致

## 概要
全導来左単位経路と制限後の既存左単位子の一致。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C)

local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 任意の指定解像度のsource同型を打ち消した、右K-flat後因子上の左単位square。 -/
lemma leftUnitRestrictionDerivedComparison_kFlat
    (Q : RightKFlatBimoduleCategory A B C) (R : RightKFlatBimoduleCategory A D C)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D C q) :
    (leftUnitRestrictionDerivedComparison A B D C F hC).app
        ((bimoduleToDerived A B C).obj Q.obj) =
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) := by
  apply (Iso.cancel_iso_hom_left
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq) _ _).1
  exact (leftUnitRestrictionDerivedComparison_model A B D C F hC Q R q hq).trans
    (leftUnitRestrictionModelPath_eq_sourceLeftUnit A B D C F hC Q R q hq)

/-- 任意のdg関手に沿い、全導来外側・中間比較の左単位経路は既存左単位子と一致する。 -/
lemma leftUnitRestrictionDerivedComparison_eq :
    leftUnitRestrictionDerivedComparison A B D C F hC =
      whiskerLeft RR (derivedBimoduleLeftUnitIso A D C hC).hom := by
  apply rightKFlatDerivedNatTrans_ext A B C hC
  intro Q
  let M := (BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj Q.obj
  let R := rightKFlatResolutionObj A D C hC M
  exact leftUnitRestrictionDerivedComparison_kFlat A B D C F hC Q R
    (bimoduleCanonicalSemifreeResolution A D C M).π
    (bimoduleCanonicalSemifreeResolution A D C M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
