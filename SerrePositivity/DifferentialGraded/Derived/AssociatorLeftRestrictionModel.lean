module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPair

/-! # 指定K-flat後二因子における全導来結合子と外側左制限 -/
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
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LRD" => Functor.obj
  (derivedBimoduleRestriction A E D E T (DGFunctor.id E) G) RT
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT

private lemma post_paste {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d : V} {x y : W} (α : a ⟶ b) (n : b ⟶ c) (p : a ⟶ d) (α' : d ⟶ c)
    (f : x ⟶ H.obj a) (s : x ⟶ y) (β : y ⟶ H.obj d)
    (ha : α ≫ n = p ≫ α') (hp : f ≫ H.map p = s ≫ β) :
    f ≫ H.map α ≫ H.map n = s ≫ β ≫ H.map α' := by
  have h := congrArg (fun k => f ≫ H.map k) ha
  simp only [H.map_comp] at h
  refine h.trans ?_
  simpa only [Category.assoc] using congrArg (fun k => k ≫ H.map α') hp

private lemma paste_associator {V : Type*} [Category* V]
    {a b c a' b' c' : V} (α : a ⟶ b) (β : b ⟶ c) (r : a ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (r' : a' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hr : r ≫ t.hom = s.hom ≫ r') (hm : α' ≫ β' = r') : α ≫ β = r := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = α ≫ n.hom ≫ β' := by rw [Category.assoc, hb]
    _ = s.hom ≫ α' ≫ β' := by rw [← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ r' := by rw [hm]
    _ = _ := hr.symm

/-- 後二因子を局所化した指定K-flatモデル上で、実際の全導来結合子が左制限と可換。 -/
lemma derivedBimoduleAssociator_leftRestriction_rightKFlat :
    (derivedBimoduleAssociator A B C E D hE hD QT LRD).hom ≫
      (derivedBimoduleComposeFunctor A B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app RT).app QT) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U =
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app RT) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT QT RT).hom L := by
  let pD := derivedBimoduleComposePairComparisonIso A B C E D hE hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  let nD := derivedBimoduleComposeNestedComparisonIso A B C E D hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  let nT := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R (Iso.refl _) (Iso.refl _)
  have ha := derivedBimoduleAssociator_comparison_fac A B C E D hE hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  have hb := derivedLeftRestriction_nested_model_square A B C E T D G hT hD Q R
  have ht := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have hp := derivedLeftRestriction_pair_model_square A B C E T D G hE hT hD Q R
  have hr := post_paste ((whiskeringRight _ _ _).obj L) _ _ _ _ _ _ _ ht hp
  have hm := rightKFlatDerivedAssociator_leftRestriction A B C E T D G Q R
  exact paste_associator _ _ _ pD nD (Functor.isoWhiskerRight nT L) _ _ _ ha
    (by simpa only [Functor.isoWhiskerRight_hom, nD, nT, Category.assoc] using hb)
    (by simpa only [Functor.isoWhiskerRight_hom, whiskeringRight, pD, nT,
      Category.assoc] using hr) hm

end SerrePositivity.DifferentialGraded.BimoduleTensor
