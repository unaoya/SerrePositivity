module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionInnerModel

/-! # 第一中間制限と全導来結合子の入れ子側のモデルsquare -/
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
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E) (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "SR" => rightKFlatCompose A D E T S R
local notation "qR" => middleRestrictionComposeAugmentation A C D E T F Q.obj S.obj R.obj q
local notation "hqR" => middleRestrictionComposeAugmentation_quasiIso A C D E T F
  Q.obj S.obj R.obj q R.property hq
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq
local notation "jC" => derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
  (Iso.refl _) (Iso.refl _)
local notation "jD" => derivedBimoduleComposeInnerComparisonIso A D E T hT S R eS (Iso.refl _)
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT
local notation "k" => NatTrans.app
  (NatTrans.app (Iso.hom (derivedBimoduleComposeRightRestrictionIso A C D E T F hT)) RT) QT

private lemma paste_nested {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d : V} {x y z t : W} (f : a ⟶ b) (u : b ⟶ c) (j : a ⟶ d) (s : c ≅ d)
    (βb : H.obj b ⟶ x) (βc : H.obj c ⟶ y) (v : x ⟶ y)
    (out : y ⟶ z) (r : H.obj d ⟶ t) (β : t ⟶ z)
    (hi : f ≫ u = j ≫ s.inv) (hn : H.map u ≫ βc = βb ≫ v)
    (hm : βc ≫ out = H.map s.hom ≫ r ≫ β) :
    H.map f ≫ βb ≫ v ≫ out = H.map j ≫ r ≫ β := by
  calc
    _ = H.map (f ≫ u) ≫ βc ≫ out := by rw [H.map_comp, Category.assoc, reassoc_of% hn]
    _ = H.map j ≫ H.map s.inv ≫ βc ≫ out := by
      rw [hi, H.map_comp, Category.assoc]
    _ = _ := by
      rw [hm, ← Category.assoc (H.map s.inv) (H.map s.hom),
        ← H.map_comp, s.inv_hom_id, H.map_id, Category.id_comp]

/-- 内側の指定モデルsquareと全導来中間比較の自然性を貼り合わせた式。 -/
lemma derivedMiddleRestriction_nested_prefix_square :
    whiskerLeft L ((HD).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U ≫
      (derivedBimoduleComposeFunctor A B C T hT).map (jC).hom ≫
      (derivedBimoduleComposeKFlatIso A B C T hT QR).hom =
    whiskerLeft L ((HD).map (jD).hom) ≫
      whiskerLeft L (derivedBimoduleComposeKFlatIso A B D T hT SR).hom ≫
      rightKFlatMiddleComparison A B C D T F QR SR qR := by
  let H := HD ⋙ (whiskeringLeft _ _ _).obj L
  let s := middleRestrictionKFlatFactorIso A C D T F QR SR qR hqR
  have hi := derivedMiddleRestriction_inner_model_square A C D E T F hT Q S R q hq
  rw [← middleRestrictionKFlatFactorIso_inv A C D T F QR SR qR hqR] at hi
  have hn := (derivedMiddleRestrictionNatTrans A B C D T F hT).naturality (jC).hom
  have hm := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B C D T F hT
    QR SR qR hqR
  rw [middleRestrictionKFlatSourceIso_hom, whiskerLeft_comp] at hm
  simp only [Category.assoc] at hm
  have h := paste_nested H k ((RI).map (jC).hom) (jD).hom s
    ((derivedMiddleRestrictionNatTrans A B C D T F hT).app U)
    ((derivedMiddleRestrictionNatTrans A B C D T F hT).app
      ((bimoduleToDerived A C T).obj (QR).obj))
    ((derivedBimoduleComposeFunctor A B C T hT).map (jC).hom)
    (derivedBimoduleComposeKFlatIso A B C T hT QR).hom
    (whiskerLeft L (derivedBimoduleComposeKFlatIso A B D T hT SR).hom)
    (rightKFlatMiddleComparison A B C D T F QR SR qR) hi hn hm
  convert h using 1 <;> rfl

/-- 入れ子合成の既存表示を通すと、実際の全導来中間比較が固定モデルの比較へ戻る。 -/
lemma derivedMiddleRestriction_nested_model_square :
    whiskerLeft L ((HD).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U ≫
      (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    whiskerLeft L (derivedBimoduleComposeNestedComparisonIso A B D E T hT S R
        eS (Iso.refl _)).hom ≫
      rightKFlatMiddleComparison A B C D T F QR SR qR := by
  have h := derivedMiddleRestriction_nested_prefix_square A B C D E T F hT Q S R q hq
  simpa only [derivedBimoduleComposeNestedComparisonIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, whiskerLeft_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
