module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionPair

/-! # 第一中間制限と実際の全導来結合子のモデル上のcoherence -/
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
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RQD" => Functor.obj
  (derivedBimoduleRestriction A D E C E F (DGFunctor.id E)) QT
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT
local notation "k" => NatTrans.app
  (NatTrans.app (Iso.hom (derivedBimoduleComposeRightRestrictionIso A C D E T F hT)) RT) QT

private lemma post_paste {V : Type*} [Category* V] {a b c d e f : V}
    (α : b ⟶ c) (t : c ⟶ d) (p : b ⟶ e) (α' : e ⟶ d)
    (γ : a ⟶ b) (s : a ⟶ f) (γ' : f ⟶ e)
    (ht : α ≫ t = p ≫ α') (hp : γ ≫ p = s ≫ γ') :
    (γ ≫ α) ≫ t = s ≫ (γ' ≫ α') := by
  rw [Category.assoc, ht, ← Category.assoc γ p, hp, Category.assoc]

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

/-- 指定した制限後K-flatモデルで、実際の全導来結合子と第一中間比較が可換。 -/
lemma derivedBimoduleAssociator_middleRestriction_model
    (S : RightKFlatBimoduleCategory A D E)
    (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT RQD RT).hom ≫
      whiskerLeft L ((derivedBimoduleComposeFunctor A B D T hT).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom := by
  let eS := middleRestrictionKFlatFactorIso A C D E F Q S q hq
  let pD := derivedBimoduleComposePairComparisonIso A B D E T hE hT S R eS (Iso.refl _)
  let nD := derivedBimoduleComposeNestedComparisonIso A B D E T hT S R eS (Iso.refl _)
  let nC := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := congrArg (fun f => whiskerLeft L f)
    (derivedBimoduleAssociator_comparison_fac A B D E T hE hT S R eS (Iso.refl _))
  simp only [whiskerLeft_comp] at ha
  have hb := derivedMiddleRestriction_nested_model_square A B C D E T F hT Q S R q hq
  have ht := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have hp := derivedMiddleRestriction_pair_model_square A B C D E T F hE hT Q S R q hq
  have hr := post_paste _ _ _ _ _ _ _ ht hp
  have hm := rightKFlatDerivedAssociator_middleRestriction A B C D E T F Q S R q
  exact paste_associator _ _ _ (Functor.isoWhiskerLeft L pD)
    (Functor.isoWhiskerLeft L nD) nC _ _ _ ha
    (by simpa only [Functor.isoWhiskerLeft_hom, nD, nC, eS, Category.assoc] using hb) hr hm

/-- 後二因子がK-flatなら、制限後には既存の標準分解を取り、追加条件なしで可換になる。 -/
lemma derivedBimoduleAssociator_middleRestriction_rightKFlat :
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT RQD RT).hom ≫
      whiskerLeft L ((derivedBimoduleComposeFunctor A B D T hT).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom := by
  let M := (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj
  exact derivedBimoduleAssociator_middleRestriction_model A B C D E T F hE hT Q R
    (rightKFlatResolutionObj A D E hE M) (bimoduleCanonicalSemifreeResolution A D E M).π
    (bimoduleCanonicalSemifreeResolution A D E M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
