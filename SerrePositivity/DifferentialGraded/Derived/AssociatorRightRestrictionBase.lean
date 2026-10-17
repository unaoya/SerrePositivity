module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFamily
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestriction

/-! # 外側右制限比較の局所化前の計算

## 概要
外側右制限比較の局所化前の計算。

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
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)

/-- 入力側の制限表示の逆、通常比較の局所化、出力側の制限表示による計算。 -/
lemma derivedComposeWithRightRestrictionIso_base_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (rightKFlatDerivedCompose A D C E Q).map
          ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
        (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫
        (middleRightRestrictionDerivedIso A B D F E).hom.app
          ((composeWith A B C E Q.obj).obj P) := by
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc]
  change _ ≫ 𝟙 _ ≫ _ ≫ _ ≫
    (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private lemma post_square {V : Type*} [Category* V] {a b c d e x y : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : a ⟶ d) (δ : d ⟶ e) (ε : e ⟶ c)
    (s : c ⟶ x) (t : e ⟶ y) (f : y ⟶ x)
    (h : α ≫ β = γ ≫ δ ≫ ε) (hn : ε ≫ s = t ≫ f) :
    α ≫ β ≫ s = γ ≫ δ ≫ t ≫ f := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [hn]

variable (T : Type s) [DGCategory A T] [Small.{u} T]

/-- 通常の結合子squareを局所化し、出力の既存右制限表示を続けた式。 -/
lemma associatorRightRestriction_localized_square
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : BimoduleCategory A E T) :
    (bimoduleToDerived A D T).map
        (associatorIso A D C E T
          (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom ≫
      (bimoduleToDerived A D T).map (composeRightRestrictionIso A B D C T F P
        (BimoduleCategory.of A C T (compose A C E T
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)))).hom ≫
      (middleRightRestrictionDerivedIso A B D F T).hom.app
        ((composeWith A B C T (BimoduleCategory.of A C T (compose A C E T
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)))).obj P) =
    (bimoduleToDerived A D T).map
        (composeMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R)) ≫
      (bimoduleToDerived A D T).map (composeRightRestrictionIso A B D E T F
        ((composeWith A B C E Q).obj P) R).hom ≫
      (middleRightRestrictionDerivedIso A B D F T).hom.app
        ((composeWith A B E T R).obj ((composeWith A B C E Q).obj P)) ≫
      (derivedBimoduleRestriction A D T B T F (DGFunctor.id T)).map
        ((bimoduleToDerived A B T).map
          (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
            (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom) := by
  let f := (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom
  have hn := (middleRightRestrictionDerivedIso A B D F T).hom.naturality f
  have hs := congrArg ((bimoduleToDerived A D T).map)
    (associatorIso_rightRestriction A B D C E T F P Q R)
  simp only [CategoryTheory.Functor.map_comp] at hs
  simp only [Functor.comp_map] at hn
  exact post_square _ _ _ _ _ _ _ _ hs hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
