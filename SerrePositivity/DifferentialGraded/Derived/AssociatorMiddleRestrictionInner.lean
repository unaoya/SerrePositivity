module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionAugmentation
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionPresentation

/-! # 中間制限後の合成増大と実際の全導来内側比較のモデルsquare -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : BimoduleCategory A C E) (S : BimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "HR" => Functor.obj (derivedBimoduleComposeFunctor A D E T hT)
  (Functor.obj (bimoduleToDerived A E T) R.obj)
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "QR" => BimoduleCategory.of A C T
  (compose A C E T (BimoduleCategory.underlying A C E Q)
    (BimoduleCategory.underlying A E T R.obj))

/-- 全導来内側右比較を増大で前置し、固定Rの計算同型で挟むと合成増大の局所化になる。 -/
lemma middleRestrictionInnerAugmentation_model_square :
    (HR).map ((bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q) ≫
      ((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app
        ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q) ≫
      (RI).map (derivedBimoduleComposeKFlatValueIso A C E T hT R Q).hom =
    (derivedBimoduleComposeKFlatValueIso A D E T hT R S).hom ≫
      (bimoduleToDerived A D T).map
        (middleRestrictionComposeAugmentation A C D E T F Q S R.obj q) ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app QR := by
  let u := (bimoduleToDerived A D E).map q ≫
    (middleRightRestrictionDerivedIso A C D F E).hom.app Q
  have hn := (derivedBimoduleComposeKFlatIso A D E T hT R).hom.naturality u
  have hm := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_model_calculation A C D E T F hT R)
    ((bimoduleToDerived A C E).obj Q)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hm
  have ha := rightKFlatMiddleComposeAugmentation_square A C D E T F Q S R q
  change (HR).map u ≫ _ ≫ _ = _
  erw [hm]
  rw [← Category.assoc ((HR).map u)]
  erw [hn]
  rw [Category.assoc, ha]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
