module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionNormalization

/-! # 指定解像度から全導来左単位子のsourceへの表示同型

## 概要
指定解像度から全導来左単位子のsourceへの表示同型。

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
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C] (F : DGFunctor A D B)
  (hC : localHomKFlat A C) (Q : RightKFlatBimoduleCategory A B C)
  (R : RightKFlatBimoduleCategory A D C)

local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B D C F) Q.obj
local notation "RR" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)

/-- 指定モデルでの合成を、制限表示を通して全導来左単位子のsourceへ送る。 -/
def leftUnitRestrictionModelSourceIso := fun q hq =>
  ((derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq).app
      ((bimoduleToDerived A D D).obj DD)).symm ≪≫
    (derivedBimoduleLeftUnitFunctor A D C hC).mapIso
      ((middleRightRestrictionDerivedIso A B D F C).app Q.obj)

private lemma paste_unit_naturality {V : Type*} [Category* V]
    {a b c d e : V} (s : a ≅ b) (p : b ⟶ c) (u : c ⟶ d)
    (v : b ⟶ e) (w : e ⟶ d) (t : a ⟶ e)
    (hn : p ≫ u = v ≫ w) (hv : v = s.inv ≫ t) :
    s.hom ≫ p ≫ u = t ≫ w := by
  rw [hn, hv]
  simp only [← Category.assoc, s.hom_inv_id, Category.id_comp]

/-- 既存の左単位子は、source表示の後でRの左単位子・増大射・制限表示に計算される。 -/
lemma leftUnitRestrictionModelSourceIso_leftUnit (q : _) (hq : _) :
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) =
    (bimoduleToDerived A D C).map ((leftUnitNatIso A D C).hom.app R.obj) ≫
      (bimoduleToDerived A D C).map q ≫
      (middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj := by
  let s := (derivedBimoduleComposeResolutionComputation A D D C hC RQ R q hq).app
    ((bimoduleToDerived A D D).obj DD)
  have hn := (derivedBimoduleLeftUnitIso A D C hC).hom.naturality
    ((middleRightRestrictionDerivedIso A B D F C).hom.app Q.obj)
  have hv := derivedBimoduleLeftUnitIso_resolution_app A D C hC RQ R q hq
  have result := paste_unit_naturality s.symm _ _ _ _ _ hn hv
  convert result using 1 <;>
    first
    | rfl
    | (simp only [leftUnitRestrictionModelSourceIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, s, Category.assoc]; try rfl)

/-- モデル経路は、同じsource表示を通した既存の全導来左単位子と一致する。 -/
lemma leftUnitRestrictionModelPath_eq_sourceLeftUnit (q : _) (hq : _) :
    leftUnitRestrictionModelPath A B D C F hC Q R q hq =
    (leftUnitRestrictionModelSourceIso A B D C F hC Q R q hq).hom ≫
      (derivedBimoduleLeftUnitIso A D C hC).hom.app
        ((RR).obj ((bimoduleToDerived A B C).obj Q.obj)) := by
  rw [leftUnitRestrictionModelPath_eq, leftUnitRestrictionModelSourceIso_leftUnit]

end SerrePositivity.DifferentialGraded.BimoduleTensor
