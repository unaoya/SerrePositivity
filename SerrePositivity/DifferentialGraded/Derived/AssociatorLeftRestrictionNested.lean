module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionInner

/-! # 外側左制限と全導来結合子の入れ子側のモデルsquare -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "QLR" => rightKFlatCompose A C E D Q LR
local notation "LQR" => Functor.obj (rightKFlatLeftRestriction A C T D G) QR
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "LC" => derivedBimoduleRestriction A C D C T (DGFunctor.id C) G
local notation "HD" => derivedBimoduleComposeFunctor A B C D hD
local notation "U" => Functor.obj
  (Functor.obj (derivedBimoduleComposeFunctor A C E T hT)
    (Functor.obj (bimoduleToDerived A E T) R.obj))
  (Functor.obj (bimoduleToDerived A C E) Q.obj)
local notation "jT" => derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
  (Iso.refl _) (Iso.refl _)

private lemma paste_nested {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d e : V} {x y z p q : W}
    (k : a ⟶ b) (u : b ⟶ c) (j : a ⟶ d) (g : d ⟶ e) (s : e ≅ c)
    (βb : H.obj b ⟶ x) (βc : H.obj c ⟶ y) (v : x ⟶ y)
    (out : y ⟶ z) (t : H.obj e ⟶ q) (r : H.obj d ⟶ p) (m : p ⟶ q) (β : q ⟶ z)
    (hi : k ≫ u = j ≫ g ≫ s.hom) (hn : H.map u ≫ βc = βb ≫ v)
    (hm : βc ≫ out = H.map s.inv ≫ t ≫ β) (hk : H.map g ≫ t = r ≫ m) :
    H.map k ≫ βb ≫ v ≫ out = H.map j ≫ r ≫ m ≫ β := by
  calc
    _ = H.map k ≫ H.map u ≫ βc ≫ out := by
      rw [← Category.assoc (H.map u) βc, hn, Category.assoc]
    _ = H.map (k ≫ u) ≫ βc ≫ out := by rw [H.map_comp, Category.assoc]
    _ = H.map j ≫ H.map g ≫ H.map s.hom ≫ βc ≫ out := by
      rw [hi, H.map_comp, H.map_comp]
      simp only [Category.assoc]
    _ = H.map j ≫ H.map g ≫ t ≫ β := by
      rw [hm, ← Category.assoc (H.map s.hom) (H.map s.inv),
        ← H.map_comp, s.hom_inv_id, H.map_id, Category.id_comp]
    _ = _ := by rw [← Category.assoc (H.map g) t, hk, Category.assoc]

/-- 内側モデルsquareと全導来比較の自然性を、入れ子表示の展開前に貼り合わせる。 -/
lemma derivedLeftRestriction_nested_prefix_square :
    (HD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U ≫
      whiskerRight ((derivedBimoduleComposeFunctor A B C T hT).map (jT).hom) L ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C T hT QR).hom L =
    (HD).map (derivedBimoduleComposeInnerComparisonIso A C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      (derivedBimoduleComposeKFlatIso A B C D hD QLR).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom := by
  have hi := derivedLeftRestriction_inner_model_square A C E T D G hT hD Q R
  have hn := (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.naturality
    (jT).hom
  have hm := derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation
    A B C T D G hT hD QR
  let g : QLR ⟶ LQR := ⟨(composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom⟩
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C D hD g
  have h := paste_nested (HD) _ _ _ _
    ((middleLeftRestrictionDerivedIso A C T D G).app (QR).obj)
    _ _ _ _ _ _ _ _ hi hn hm hk
  convert h using 1 <;> rfl

/-- 全導来比較の入れ子側は、既存の入れ子表示を通して固定K-flatモデルの比較に戻る。 -/
lemma derivedLeftRestriction_nested_model_square :
    (HD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U ≫
      whiskerRight (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom L =
    (derivedBimoduleComposeNestedComparisonIso A B C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom := by
  have h := derivedLeftRestriction_nested_prefix_square A B C E T D G hT hD Q R
  simpa only [derivedBimoduleComposeNestedComparisonIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, whiskerRight_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
