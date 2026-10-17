module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionKFlat
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionResolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison

/-! # 外側右制限の全導来比較を固定K-flat合成の表示へ計算する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D E B E F (DGFunctor.id E)

lemma rightRestrictionDerivedComposeSourceBaseIso_hom_app :
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q =
      whiskerLeft RI (derivedBimoduleComposeKFlatIso A D C E hE Q).hom := by
  simp only [rightRestrictionDerivedComposeSourceBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

lemma rightRestrictionDerivedComposeTargetBaseIso_hom_app :
    (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom RO := by
  simp only [rightRestrictionDerivedComposeTargetBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- 全導来右比較と固定K-flat右比較を結ぶ、任意の導来前因子に自然なsquare。 -/
lemma derivedBimoduleComposeRightRestrictionIso_model_calculation :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom RO =
    whiskerLeft RI (derivedBimoduleComposeKFlatIso A D C E hE Q).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C E F Q).hom := by
  have h := derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE Q
  rw [rightRestrictionDerivedComposeSourceBaseIso_hom_app,
    rightRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
