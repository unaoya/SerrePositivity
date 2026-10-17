module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionResolved
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionBase

/-! # 第二中間圏の指定K-flatモデルと導来結合子のcoherence -/
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
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)
  (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)

local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "QS" => rightKFlatCompose A C D T LQ S
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "g" => middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q

/-- 第二中間比較と外側左比較は、固定K-flat導来結合子の二経路を同一視する。 -/
lemma rightKFlatDerivedAssociator_secondMiddleRestriction :
    whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
        (rightKFlatDerivedCompose A B D T S) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatMiddleComparison A B E D T F R S q) ≫
      (rightKFlatDerivedAssociator A B C E T Q R).hom =
    (rightKFlatDerivedAssociator A B C D T LQ S).hom ≫
      rightKFlatDerivedMap A B C T (Q := QS) (Q' := QR) g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  have hβ := derivedComposeWithLeftRestrictionIso_base_app A B C E D F Q P
  have hm := rightKFlatMiddleComparison_base_app A B E D T F R S q
    ((composeWith A B C E Q.obj).obj P)
  have hα := rightKFlatDerivedAssociator_base_app A B C E T Q R P
  have hα' := rightKFlatDerivedAssociator_base_app A B C D T LQ S P
  have hg := rightKFlatDerivedMap_base_app A B C T (Q := QS) (Q' := QR) g P
  rw [hβ, hα, hα', hg]
  erw [hm]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hc := congrArg (fun k => (rightKFlatDerivedCompose A B D T S).map k)
    ((middleLeftRestrictionDerivedIso A B E D F).hom_inv_id_app
      ((composeWith A B C E Q.obj).obj P))
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [reassoc_of% hc]
  have hmap := rightKFlatDerivedCompose_map_base A B D T S
    (composeLeftRestrictionIso A B C E D F P Q.obj).hom
  rw [hmap]
  have hs := congrArg ((bimoduleToDerived A B T).map)
    (associatorIso_secondMiddleRestriction_resolved A B C D E T F P Q.obj R.obj S.obj q)
  simp only [CategoryTheory.Functor.map_comp] at hs
  convert hs using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
