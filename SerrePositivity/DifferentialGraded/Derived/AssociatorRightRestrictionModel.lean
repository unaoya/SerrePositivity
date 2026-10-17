module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionPair

/-! # 指定K-flat後二因子における全導来結合子と外側右制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT

private lemma paste_rectangle {V : Type*} [Category* V] {a b c d a' b' c' d' : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : a ⟶ d) (δ : d ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c') (m : d ≅ d')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (γ' : a' ⟶ d') (δ' : d' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hc : γ ≫ m.hom = s.hom ≫ γ') (hd : δ ≫ t.hom = m.hom ≫ δ')
    (hm : α' ≫ β' = γ' ≫ δ') : α ≫ β = γ ≫ δ := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = s.hom ≫ α' ≫ β' := by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ γ' ≫ δ' := by rw [hm]
    _ = (γ ≫ δ) ≫ t.hom := by
      rw [Category.assoc γ δ t.hom, hd, ← Category.assoc γ, hc, Category.assoc]

/-- 指定右K-flatモデルを局所化した後二因子で、実際の全導来結合子が右制限と可換。 -/
lemma derivedBimoduleAssociator_rightRestriction_rightKFlat :
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT QT RT).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app U =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT QT RT).hom RO := by
  let pD := derivedBimoduleComposePairComparisonIso A D C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nD := derivedBimoduleComposeNestedComparisonIso A D C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  let pB := derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nB := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := congrArg (fun k => whiskerLeft RI k)
    (derivedBimoduleAssociator_comparison_fac A D C E T hE hT Q R
      (Iso.refl _) (Iso.refl _))
  have hd := congrArg (fun k => whiskerRight k RO)
    (derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
      (Iso.refl _) (Iso.refl _))
  simp only [whiskerLeft_comp] at ha
  simp only [whiskerRight_comp] at hd
  have hb := derivedRightRestriction_nested_model_square A B D C E T F hT Q R
  have hc := derivedRightRestriction_pair_model_square A B D C E T F hE hT Q R
  have hm := rightKFlatDerivedAssociator_rightRestriction A B D C E T F Q R
  simpa only [Category.assoc] using paste_rectangle _ _
    (whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT)) _
    (Functor.isoWhiskerLeft RI pD)
    (Functor.isoWhiskerLeft RI nD) (Functor.isoWhiskerRight nB RO)
    (Functor.isoWhiskerRight pB RO) _ _ _ _ ha hb
    (by simpa only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      pD, pB, Category.assoc] using hc) hd
    (by simpa only [Category.assoc] using hm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
