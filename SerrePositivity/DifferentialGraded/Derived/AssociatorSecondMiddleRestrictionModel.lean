module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionPair

/-! # 第二中間制限と実際の全導来結合子のモデル上のcoherence

## 概要
第二中間制限と実際の全導来結合子のモデル上のcoherence。

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
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "LQD" => Functor.obj
  (derivedBimoduleRestriction A C D C E (DGFunctor.id C) F) QT
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT

private lemma post_paste {V : Type*} [Category* V] {a b c d e f : V}
    (α : a ⟶ b) (γ : b ⟶ c) (n : b ⟶ d) (t : c ⟶ e)
    (p : a ⟶ f) (α' : f ⟶ d) (γ' : d ⟶ e)
    (ha : α ≫ n = p ≫ α') (hb : γ ≫ t = n ≫ γ') :
    (α ≫ γ) ≫ t = p ≫ (α' ≫ γ') := by
  rw [Category.assoc, hb, ← Category.assoc α n, ha, Category.assoc]

private lemma paste_associator {V : Type*} [Category* V]
    {a b c a' b' c' : V} (α : a ⟶ b) (β : b ⟶ c) (r : a ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (r' : a' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hr : r ≫ t.hom = s.hom ≫ r') (hm : α' ≫ β' = r') : α ≫ β = r := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = s.hom ≫ α' ≫ β' := by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ r' := by rw [hm]
    _ = _ := hr.symm

/-- 指定した制限後K-flatモデルで、実際の全導来結合子と第二中間比較が可換。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction_model
    (S : RightKFlatBimoduleCategory A D T)
    (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
    (hq : BimoduleCategory.quasiIso A D T q) :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom =
    (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT) := by
  let eS := middleRestrictionKFlatFactorIso A E D T F R S q hq
  let eQ := ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm
  let pD := derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S eQ eS
  let nD := derivedBimoduleComposeNestedComparisonIso A B C D T hT LQ S eQ eS
  let pC := derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nC := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := derivedSecondMiddleRestriction_pair_model_square A B C D E T F hD hT Q R S q hq hE
  have hb := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have ht := derivedBimoduleAssociator_comparison_fac A B C D T hD hT LQ S eQ eS
  have hn := derivedSecondMiddleRestriction_nested_model_square A B C D E T F hT Q R S q hq
  have hr := post_paste _ _ _ _ _ _ _ ht hn
  have hm := rightKFlatDerivedAssociator_secondMiddleRestriction A B C D E T F Q R S q
  let a := whiskerRight
      ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
      ((HD).obj RRD) ≫
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
      ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT)
  let a' := whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
      (rightKFlatDerivedCompose A B D T S) ≫
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
      (rightKFlatMiddleComparison A B E D T F R S q)
  let r := (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
    (derivedBimoduleComposeFunctor A B C T hT).map
      (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT)
  let r' := (rightKFlatDerivedAssociator A B C D T LQ S).hom ≫
    rightKFlatDerivedMap A B C T (Q := rightKFlatCompose A C D T LQ S)
      (Q' := rightKFlatCompose A C E T Q R)
      (middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q)
  have h := paste_associator a (derivedBimoduleAssociator A B C E T hE hT QT RT).hom r
    pD pC nC a' (rightKFlatDerivedAssociator A B C E T Q R).hom r'
    (by simpa only [a, a', pC, pD, eQ, eS, Category.assoc] using ha) hb
    (by simpa only [r, r', eQ, eS, nD, nC, pD, leftRestrictionDerivedComposeTarget,
      Functor.comp_obj, Category.assoc] using hr)
    (by simpa only [a', r', Category.assoc] using hm)
  simpa only [a, r, Category.assoc] using h

/-- 制限後には既存の標準K-flat分解を取り、後二因子のモデル以外の条件を追加せず可換にする。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction_rightKFlat :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom =
    (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT) := by
  let M := (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj
  exact derivedBimoduleAssociator_secondMiddleRestriction_model A B C D E T F hE hD hT Q R
    (rightKFlatResolutionObj A D T hT M) (bimoduleCanonicalSemifreeResolution A D T M).π
    (bimoduleCanonicalSemifreeResolution A D T M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
