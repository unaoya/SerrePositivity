module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedFunctor

/-! # 元の通常射と全族を保つ点つき単位
概要：写した通常射を厳密に回収し、元の単位の成分を全 basedHom 作用に接続する。
方針：単位の自然性と閉 Hom の回収を標準点つき豊穣へ反映する。
規約：元の全入力を保持する。使われ方：Ex∞ 置換と元の K 模型の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の通常の基点固定射を、同じ基礎関手で写した点つき射。 -/
def coaugmentedPointedMap {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    coaugmentedPointedObject F η X ⟶ coaugmentedPointedObject F η Y := by
  let g : X.obj ⟶ Y.obj := f
  refine Under.homMk (F.map g.right) ?_
  have hn := η.naturality g.right
  change g.right ≫ η.app Y.obj.right = η.app X.obj.right ≫ F.map g.right at hn
  change (X.obj.hom ≫ η.app X.obj.right) ≫ F.map g.right = Y.obj.hom ≫ η.app Y.obj.right
  rw [Category.assoc, ← hn, ← Category.assoc, Under.w g]

/-- 元の基点から単位の像の基点への、同じ単位の実際の成分。 -/
def coaugmentedPointedUnit (X : PointedSSetObject.{u}) :
    X ⟶ coaugmentedPointedObject F η X := Under.homMk (η.app X.obj.right) rfl

/-- 元の通常の点つき射では、同じ写した点つき射の標準豊穣表示を回収する。 -/
lemma coaugmentedPointedEnrichedFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet.{u} f ≫ (coaugmentedPointedEnrichedFunctor F η).map X Y =
      eHomEquiv SSet.{u} (coaugmentedPointedMap F η f) := by
  have h : eHomEquiv SSet.{u} f ≫ (coaugmentedPointedInternalFunctor F η).map X Y =
      curry' (F.map (show X.obj ⟶ Y.obj from f).right) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ coaugmentedClosedFamilyMap F η X.obj.right Y.obj.right)
        (pointedSSetObjectClosedForget_hom f)).trans
          (coaugmentedClosedFamilyMap_hom F η (show X.obj ⟶ Y.obj from f).right))
  exact pointedEnrichedFunctorOfAction_hom _ _ _ _ _ _ f _
    (internalEnrichedAction_hom (coaugmentedPointedInternalFunctor F η) f _ h)

/-- 単位の同じ成分は、元の全基点固定写像族の作用と厳密に可換する。 -/
lemma coaugmentedPointedUnit_action (X Y : PointedSSetObject.{u}) :
    ((show X.obj ⟶ (coaugmentedPointedObject F η X).obj from
      coaugmentedPointedUnit F η X).right ▷ (X ⟶[SSet.{u}] Y)) ≫
        uncurry ((coaugmentedPointedInternalFunctor F η).map X Y) =
      uncurry (PointedObject.basedHomι X.obj Y.obj) ≫
        (show Y.obj ⟶ (coaugmentedPointedObject F η Y).obj from
          coaugmentedPointedUnit F η Y).right :=
  coaugmentedClosedFamilyMap_action F η (PointedObject.basedHomι X.obj Y.obj)

/-- 基礎単体集合へ忘れると、同じ元の全閉 Hom 作用の厳密豊穣関手になる。 -/
lemma coaugmentedPointedEnrichedFunctor_forget :
    (coaugmentedPointedEnrichedFunctor F η).comp SSet pointedSSetObjectClosedForget =
      coaugmentedPointedInternalFunctor F η := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro X Y
  exact (Category.comp_id _).trans
    ((coaugmentedPointedFamilyMap_inclusion F η X Y).trans (curry_uncurry _))

end SerrePositivity.KST.SConstruction
