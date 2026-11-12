module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionStrength
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedFamilyStrength

/-! # suspension 比較と全基点固定写像族の厳密可換性
概要：同じ元の前向き比較が、全単体の点つき写像族の作用と厳密に可換することを示す。
方針：元の円の直積商がエピであることを使い、strength の商射上の全族公式へ帰着する。
規約：通常射だけの自然性ではない。使われ方：Ex∞ の厳密豊穣 suspension 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の円の商射上で、比較後の全作用は同じ strength の作用を回収する。 -/
lemma coaugmentedPointedSuspensionComparison_family_source_quotient {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
      (coaugmentedPointedObject F η X).obj ▷ P) ≫
      (((coaugmentedPointedSuspensionComparison F η X).right ▷ P) ≫
      uncurry (((a ≫ (Spectra.suspensionHom X.obj Y.obj).right) ≫
        (coaugmentedPointedEnrichedFunctor F η).map
          (pointedSSetSuspensionObject X) (pointedSSetSuspensionObject Y)) ≫
        PointedObject.basedHomι
          (coaugmentedPointedObject F η (pointedSSetSuspensionObject X)).obj
          (coaugmentedPointedObject F η (pointedSSetSuspensionObject Y)).obj)) =
    ((coaugmentedTensorLeftStrength F η PointedSimplicialSet.circle.{u}.right X.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X.obj)) ▷ P) ≫
      coaugmentedTensorRightStrength F η (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj).right P ≫
      F.map (uncurry (a ≫ (Spectra.suspensionHom X.obj Y.obj).right ≫
        PointedObject.basedHomι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y.obj))) := by
  erw [← Category.assoc, ← comp_whiskerRight,
    coaugmentedPointedSuspensionComparison_quotient_strength,
    coaugmentedPointedFamily_strength]
  rfl

/-- 元の円の商射上で、全作用後の比較も同じ strength の式を回収する。 -/
lemma coaugmentedPointedSuspensionComparison_family_target_quotient {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
      (coaugmentedPointedObject F η X).obj ▷ P) ≫
      (uncurry ((a ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y) ≫
      (Spectra.suspensionHom (coaugmentedPointedObject F η X).obj
        (coaugmentedPointedObject F η Y).obj).right ≫
      PointedObject.basedHomι
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η X).obj)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η Y).obj)) ≫
      (coaugmentedPointedSuspensionComparison F η Y).right) =
    (α_ PointedSimplicialSet.circle.{u}.right (F.obj X.obj.right) P).hom ≫
      (PointedSimplicialSet.circle.{u}.right ◁
        (coaugmentedTensorRightStrength F η X.obj.right P ≫
          F.map (uncurry (a ≫ PointedObject.basedHomι X.obj Y.obj)))) ≫
      coaugmentedTensorLeftStrength F η PointedSimplicialSet.circle.{u}.right Y.obj.right ≫
      F.map (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} Y.obj) := by
  exact suspensionFamily_evaluation_post
    (coaugmentedPointedObject F η X).obj (coaugmentedPointedObject F η Y).obj
    (coaugmentedPointedObject F η (pointedSSetSuspensionObject Y)).obj
    (a ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y)
    (coaugmentedPointedSuspensionComparison F η Y) _ _
    (coaugmentedPointedFamily_strength F η X Y a)
    (coaugmentedPointedSuspensionComparison_quotient_strength F η Y)

/-- 前向き suspension 比較は、任意の単体集合をパラメータとする全点つき族に自然。 -/
lemma coaugmentedPointedSuspensionComparison_family_action {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    ((coaugmentedPointedSuspensionComparison F η X).right ▷ P) ≫
      uncurry (((a ≫ (Spectra.suspensionHom X.obj Y.obj).right) ≫
        (coaugmentedPointedEnrichedFunctor F η).map
          (pointedSSetSuspensionObject X) (pointedSSetSuspensionObject Y)) ≫
        PointedObject.basedHomι
          (coaugmentedPointedObject F η (pointedSSetSuspensionObject X)).obj
          (coaugmentedPointedObject F η (pointedSSetSuspensionObject Y)).obj) =
    uncurry ((a ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y) ≫
      (Spectra.suspensionHom (coaugmentedPointedObject F η X).obj
        (coaugmentedPointedObject F η Y).obj).right ≫
      PointedObject.basedHomι
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η X).obj)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (coaugmentedPointedObject F η Y).obj)) ≫
      (coaugmentedPointedSuspensionComparison F η Y).right := by
  let q := PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
    (coaugmentedPointedObject F η X).obj
  have : Epi q := Under.epi_right_of_epi
    (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
      (coaugmentedPointedObject F η X).obj)
  have : Epi (q ▷ P) := (tensorRight P).map_epi q
  apply (cancel_epi (q ▷ P)).mp
  exact (coaugmentedPointedSuspensionComparison_family_source_quotient F η X Y a).trans
    ((coaugmentedPointedSuspensionStrength_family F η X Y a).trans
      (coaugmentedPointedSuspensionComparison_family_target_quotient F η X Y a).symm)

end SerrePositivity.KST.SConstruction
