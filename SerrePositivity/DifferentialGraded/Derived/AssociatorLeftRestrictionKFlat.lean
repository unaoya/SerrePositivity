module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionBase

/-! # 外側左制限は固定右K-flat因子の導来結合子を保つ -/
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
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "QLR" => rightKFlatCompose A C E D Q LR
local notation "LQR" => Functor.obj (rightKFlatLeftRestriction A C T D G) QR
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G

/-- 固定後二因子では、左制限の通常比較を導来合成へ送った射を通して結合子が可換。 -/
lemma rightKFlatDerivedAssociator_leftRestriction :
    (rightKFlatDerivedAssociator A B C E D Q LR).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom =
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithLeftRestrictionIso A B E T D G R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E T Q R).hom L := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [rightKFlatDerivedAssociator_base_app, rightKFlatDerivedMap_base_app,
    derivedComposeWithLeftRestrictionIso_base_app]
  let PQ := (composeWith A B C E Q.obj).obj P
  have hβ := derivedComposeWithLeftRestrictionIso_base_app A B E T D G R PQ
  erw [hβ, rightKFlatDerivedAssociator_base_app]
  let f := (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E T R.obj)).hom
  have hn := (middleLeftRestrictionDerivedIso A B T D G).hom.naturality f
  have hs := congrArg ((bimoduleToDerived A B D).map)
    (associatorIso_leftRestriction A B C E T D G P Q.obj R.obj)
  simp only [CategoryTheory.Functor.map_comp] at hs
  have h := congrArg (fun k => k ≫
    (middleLeftRestrictionDerivedIso A B T D G).hom.app
      ((composeWith A B C T (QR).obj).obj P)) hs
  simp only [Category.assoc] at h
  erw [hn] at h
  simp only [Functor.comp_map] at h
  simp only [Category.assoc]
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
