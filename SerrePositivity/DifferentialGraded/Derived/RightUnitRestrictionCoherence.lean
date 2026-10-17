module
public import SerrePositivity.DifferentialGraded.Derived.RightUnitRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleKFlatIndependence

/-! # 既存の全導来中間比較と右単位子の可換図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D D hD
local notation "ID" => Functor.obj (bimoduleToDerived A D D)
  (BimoduleCategory.of A D D (Bimodule.diagonal A D))
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- 既存の外側左制限比較と右単位子の経路を、通常のbimodule射に計算する。 -/
lemma rightUnitRestriction_target_calculation (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P)) =
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫
      (bimoduleToDerived A B D).map
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app_calc, derivedRightUnitIso_base_app]
  change _ ≫ (𝟙 _ ≫ _ ≫ _ ≫ (L).map (𝟙 _)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  let f : (composeWith A B C C (rightKFlatDiagonal A C).obj).obj P ⟶ P :=
    (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom
  have hn := (middleLeftRestrictionDerivedIso A B C D F).hom.naturality f
  change (bimoduleToDerived A B D).map
      ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map f) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P =
    (middleLeftRestrictionDerivedIso A B C D F).hom.app
      ((composeWith A B C C (rightKFlatDiagonal A C).obj).obj P) ≫
      (L).map ((bimoduleToDerived A B C).map f) at hn
  simpa only [Category.assoc] using
    congrArg (fun k => (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (bimoduleToDerived A B D).map
        (composeLeftRestrictionIso A B C C D F P (rightKFlatDiagonal A C).obj).hom ≫ k) hn.symm

/-- 右単位squareの全導来比較を、元の前因子上のモデル計算へ帰着する。 -/
lemma rightUnitRestrictionDerivedComparison_base_fac (hF : HomQuasiIso F)
    (P : BimoduleCategory A B C) :
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightUnitRestrictionDerivedComparison A B C D F hD).app
        ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleRightUnitIso A B D hD).hom.app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleLeftRestrictionDerivedIso A B C D F).hom.app P := by
  have hm := rightUnitRestrictionMiddleMap_base_fac A B C D F hD P
  have hs := derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D D F hD QF
    (rightKFlatDiagonal A D) (Bimodule.diagonalRestrictionMap A D C F)
    ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F).2 hF) P
  have ht := rightUnitRestriction_target_calculation A B C D F hD P
  have hu := derivedRightUnitRestriction_model A B C D F hD hF P
  simp only [rightUnitRestrictionDerivedComparison, NatTrans.comp_app, whiskerRight_app]
  have h := congrArg (fun k => k ≫
    (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P))) hm
  simp only [Category.assoc] at h
  refine h.trans ?_
  have hs' := congrArg (fun k => ((HD).map ((bimoduleToDerived A D D).map
      (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫ k ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD QF P).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (L).map ((derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P))) hs.symm
  refine hs'.trans ?_
  have ht' := congrArg (fun k => ((HD).map ((bimoduleToDerived A D D).map
      (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionComparison A B C D D F hD P QF (rightKFlatDiagonal A D)
        (Bimodule.diagonalRestrictionMap A D C F)
        ((Bimodule.diagonalRestrictionMap_quasiIso_iff A D C F).2 hF) ≫ k) ht
  refine ht'.trans ?_
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (middleLeftRestrictionDerivedIso A B C D F).hom.app P) hu

/-- 任意の導来前因子で、対角・中間・外側比較の経路は制限後の右単位子と一致する。 -/
lemma rightUnitRestrictionDerivedComparison_eq (hF : HomQuasiIso F) :
    rightUnitRestrictionDerivedComparison A B C D F hD =
      whiskerLeft L (derivedBimoduleRightUnitIso A B D hD).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  apply (Iso.cancel_iso_hom_left
    (((HD).obj ID).mapIso ((middleLeftRestrictionDerivedIso A B C D F).app P)) _ _).1
  change ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫ _ =
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (derivedBimoduleRightUnitIso A B D hD).hom.app
        ((L).obj ((bimoduleToDerived A B C).obj P))
  rw [rightUnitRestrictionDerivedComparison_base_fac A B C D F hD hF P]
  exact ((derivedBimoduleRightUnitIso A B D hD).hom.naturality
    ((middleLeftRestrictionDerivedIso A B C D F).hom.app P)).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
