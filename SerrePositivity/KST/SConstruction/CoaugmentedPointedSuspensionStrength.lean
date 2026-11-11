module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspension
public import SerrePositivity.KST.SConstruction.CoaugmentedTensorStrengthNaturality
public import SerrePositivity.KST.SConstruction.SuspensionFamilyEvaluation

/-! # 同じ suspension 比較の元の商射上の全パラメータ整合性
概要：元の円と全入力族を保つ作用の可換性を、同じ tensor strength の像へ移す。
方針：元の suspension 族の評価式と、商射上の strength の結合則を合成する。
規約：パラメータは任意の単体集合。使われ方：標準点つき豊穣の全 Hom 自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の直積商射からの比較は、同じ左 strength と元の商射の像の合成。 -/
lemma coaugmentedPointedSuspensionComparison_quotient_strength (X : PointedSSetObject.{u}) :
    PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
      (coaugmentedPointedObject F η X).obj ≫
      (coaugmentedPointedSuspensionComparison F η X).right =
    coaugmentedTensorLeftStrength F η PointedSimplicialSet.circle.{u}.right X.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X.obj) := by
  simpa only [coaugmentedTensorLeftStrength, tensorHom_id, Category.assoc] using
    coaugmentedPointedSuspensionComparison_quotient F η X

omit [NatTrans.IsMonoidal η] in
/-- 元の円の商射上で、任意の全族の suspension と同じ strength の比較が可換する。 -/
lemma coaugmentedPointedSuspensionStrength_family {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    ((coaugmentedTensorLeftStrength F η PointedSimplicialSet.circle.{u}.right X.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X.obj)) ▷ P) ≫
      coaugmentedTensorRightStrength F η (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj).right P ≫
      F.map (uncurry (a ≫ (Spectra.suspensionHom X.obj Y.obj).right ≫
        PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y.obj))) =
    (α_ PointedSimplicialSet.circle.{u}.right (F.obj X.obj.right) P).hom ≫
      (PointedSimplicialSet.circle.{u}.right ◁
        (coaugmentedTensorRightStrength F η X.obj.right P ≫
          F.map (uncurry (a ≫ PointedObject.basedHomι X.obj Y.obj)))) ≫
      coaugmentedTensorLeftStrength F η PointedSimplicialSet.circle.{u}.right Y.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} Y.obj) :=
  coaugmentedTensorStrength_quotient_action F η
    (uncurry (a ≫ PointedObject.basedHomι X.obj Y.obj)) _ _ _
    (suspensionFamily_evaluation X.obj Y.obj a)

end SerrePositivity.KST.SConstruction
