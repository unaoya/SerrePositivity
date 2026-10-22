module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionFamily
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionFunctor
public import SerrePositivity.KST.SConstruction.PointedStrictTransformationOfAction

/-! # 同じ suspension 比較の厳密豊穣自然変換
概要：全基点固定写像族に自然な比較を、同じ点つき値の厳密単体的自然変換へ束ねる。
方針：元の全 Hom をパラメータにし、元の実作用の可換性を標準豊穣へ反映する。
規約：自然な厳密逆は選ばない。使われ方：Ex∞ 後の BF span の豊穣関手化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.Monoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の置換を施した値の、元の円による suspension の厳密豊穣関手。 -/
def coaugmentedThenSuspensionFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  (coaugmentedPointedEnrichedFunctor F η).comp SSet pointedSSetSuspensionEnrichedFunctor

/-- 元の suspension に同じ置換を施す厳密豊穣関手。 -/
def suspensionThenCoaugmentedFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  pointedSSetSuspensionEnrichedFunctor.comp SSet (coaugmentedPointedEnrichedFunctor F η)

/-- 同じ前向き比較の全 Hom の実作用に関する厳密自然性。 -/
lemma coaugmentedPointedSuspensionTransformation_action (X Y : PointedSSetObject.{u}) :
    ((coaugmentedPointedSuspensionComparison F η X).right ▷ (X ⟶[SSet.{u}] Y)) ≫
      uncurry ((suspensionThenCoaugmentedFunctor F η).map X Y ≫
        PointedObject.basedHomι
          ((suspensionThenCoaugmentedFunctor F η).obj X).obj
          ((suspensionThenCoaugmentedFunctor F η).obj Y).obj) =
    uncurry ((coaugmentedThenSuspensionFunctor F η).map X Y ≫
      PointedObject.basedHomι
        ((coaugmentedThenSuspensionFunctor F η).obj X).obj
        ((coaugmentedThenSuspensionFunctor F η).obj Y).obj) ≫
      (coaugmentedPointedSuspensionComparison F η Y).right := by
  ext n t
  exact types_congr_hom (NatTrans.congr_app
    (coaugmentedPointedSuspensionComparison_family_action F η X Y (𝟙 _)) n) t

/-- 同じ元の前向き suspension 比較を全 Hom 上で束ねた、厳密単体的自然変換。 -/
def coaugmentedPointedSuspensionTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (coaugmentedThenSuspensionFunctor F η) (suspensionThenCoaugmentedFunctor F η) :=
  pointedStrictTransformationOfAction _ _
    (fun X => coaugmentedPointedSuspensionComparison F η X)
    (coaugmentedPointedSuspensionTransformation_action F η)

/-- 厳密豊穣自然変換の成分は、元の同じ円・単位・smash 比較からの実比較。 -/
lemma coaugmentedPointedSuspensionTransformation_app (X : PointedSSetObject.{u}) :
    (coaugmentedPointedSuspensionTransformation F η).app X =
      eHomEquiv SSet
        (show (coaugmentedThenSuspensionFunctor F η).obj X ⟶
          (suspensionThenCoaugmentedFunctor F η).obj X from
            coaugmentedPointedSuspensionComparison F η X) := rfl

end SerrePositivity.KST.SConstruction
