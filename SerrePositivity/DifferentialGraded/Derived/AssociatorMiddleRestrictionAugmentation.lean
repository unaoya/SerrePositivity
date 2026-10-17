module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionResolved
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionBase

/-! # 制限後の増大の合成と固定K-flat外側右比較の可換square

## 概要
制限後の増大の合成と固定K-flat外側右比較の可換square。

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
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (Q : BimoduleCategory A C E) (S : BimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "KR" => rightKFlatDerivedCompose A D E T R
local notation "QR" => BimoduleCategory.of A C T
  (compose A C E T (BimoduleCategory.underlying A C E Q)
    (BimoduleCategory.underlying A E T R.obj))

/-- 任意の増大の合成は、入力・出力の既存制限表示と固定K-flat右比較を保つ。 -/
lemma rightKFlatMiddleComposeAugmentation_square :
    (KR).map ((bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q) ≫
      (derivedComposeWithRightRestrictionIso A C D E T F R).hom.app
        ((bimoduleToDerived A C E).obj Q) =
    (bimoduleToDerived A D T).map
        (middleRestrictionComposeAugmentation A C D E T F Q S R.obj q) ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app QR := by
  have hc := congrArg (fun k => (KR).map k)
    ((middleRightRestrictionDerivedIso A C D F E).hom_inv_id_app Q)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [derivedComposeWithRightRestrictionIso_base_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  have hm := rightKFlatDerivedCompose_map_base A D E T R q
  rw [hm]
  simp only [middleRestrictionComposeAugmentation, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
