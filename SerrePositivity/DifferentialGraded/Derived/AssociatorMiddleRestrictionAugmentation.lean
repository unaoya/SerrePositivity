module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionResolved
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionBase

/-! # 制限後の増大の合成と固定K-flat外側右比較の可換square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (Q : BimoduleCategory A C E) (S : BimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "KR" => rightKFlatDerivedCompose A D E T R
local notation "QR" => BimoduleCategory.of A C T
  (compose A C E T (BimoduleCategory.underlying A C E Q)
    (BimoduleCategory.underlying A E T R.obj))

/-- 任意の増大の合成は、入力・出力の既存制限表示と固定K-flat右比較を保つ。 -/
lemma rightKFlatMiddleComposeAugmentation_square :
    (KR).map ((bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q) ≫
      (derivedComposeWithRightRestrictionIso A C D E T F R).hom.app
        ((bimoduleToDerived A C E).obj Q) =
    (bimoduleToDerived A D T).map
        (middleRestrictionComposeAugmentation A C D E T F Q S R.obj q) ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app QR := by
  have hc := congrArg (fun k => (KR).map k)
    ((middleRightRestrictionDerivedIso A C D F E).hom_inv_id_app Q)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [derivedComposeWithRightRestrictionIso_base_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  have hm := rightKFlatDerivedCompose_map_base A D E T R q
  rw [hm]
  simp only [middleRestrictionComposeAugmentation, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
