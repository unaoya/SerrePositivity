module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionPresentation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison

/-! # 外側左制限と導来結合子の内側合成のモデル比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (D : Type t) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "L" => derivedBimoduleRestriction A C D C T (DGFunctor.id C) G

/-- 実際の全導来左比較は、内側合成の既存モデル表示と通常左制限比較に整合する。 -/
lemma derivedLeftRestriction_inner_model_square :
    ((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
        ((bimoduleToDerived A E T).obj R.obj)).app
          ((bimoduleToDerived A C E).obj Q.obj) ≫
      (L).map (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      (bimoduleToDerived A C D).map
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (middleLeftRestrictionDerivedIso A C T D G).hom.app (QR).obj := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
    A C E T D G hT hD R Q.obj
  simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.refl_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc]
  convert h using 1
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
