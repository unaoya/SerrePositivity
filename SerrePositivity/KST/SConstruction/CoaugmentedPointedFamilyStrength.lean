module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedMaps
public import SerrePositivity.KST.SConstruction.CoaugmentedTensorStrength

/-! # 元の点つき全族の作用を tensor strength で回収する
概要：標準 basedHom 族の写した実作用を、元の同じパラメータ作用の像で表す。
方針：元の basedHom 包含後の式を、一般の閉 Hom の strength 評価へ移す。
規約：全パラメータ・全単体を保持する。使われ方：suspension 比較の全族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 同じ点つき全 Hom 作用の包含後には、元の閉 Hom 比較を厳密に回収する。 -/
lemma coaugmentedPointedEnrichedFunctor_closed_inclusion (X Y : PointedSSetObject.{u}) :
    (coaugmentedPointedEnrichedFunctor F η).map X Y ≫
      PointedObject.basedHomι (coaugmentedPointedObject F η X).obj
        (coaugmentedPointedObject F η Y).obj =
    PointedObject.basedHomι X.obj Y.obj ≫
      coaugmentedClosedFamilyMap F η X.obj.right Y.obj.right :=
  (coaugmentedPointedFamilyMap_inclusion F η X Y).trans (curry_uncurry _)

/-- 任意の全パラメータ族でも、同じ包含後の閉 Hom 比較を回収する。 -/
lemma coaugmentedPointedFamily_closed_inclusion {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    (a ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y) ≫
      PointedObject.basedHomι (coaugmentedPointedObject F η X).obj
        (coaugmentedPointedObject F η Y).obj =
    (a ≫ PointedObject.basedHomι X.obj Y.obj) ≫
      coaugmentedClosedFamilyMap F η X.obj.right Y.obj.right :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q)
      (coaugmentedPointedEnrichedFunctor_closed_inclusion F η X Y)).trans
        (Category.assoc _ _ _).symm)

/-- 任意の点つき全パラメータ族の像の実作用は、元の作用の同じ strength による像。 -/
lemma coaugmentedPointedFamily_strength {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    uncurry ((a ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y) ≫
      PointedObject.basedHomι (coaugmentedPointedObject F η X).obj
        (coaugmentedPointedObject F η Y).obj) =
    coaugmentedTensorRightStrength F η X.obj.right P ≫
      F.map (uncurry (a ≫ PointedObject.basedHomι X.obj Y.obj)) := by
  exact (congrArg (uncurry (C := SSet.{u}))
    (coaugmentedPointedFamily_closed_inclusion F η X Y a)).trans
      (coaugmentedClosedFamilyMap_strength F η (a ≫ PointedObject.basedHomι X.obj Y.obj))

end SerrePositivity.KST.SConstruction
