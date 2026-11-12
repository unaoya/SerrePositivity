module
public import SerrePositivity.KST.Spectra.FreeInterval
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletion
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderPushoutProperties

/-! # 一般の実円柱 Kan 値の単射性と弱比較
概要：元の両標的から Kan 値への比較は単射で、左脚が弱同値なら右比較も弱同値。
方針：同じ実押し出しの性質へ、同じ anodyne 単位を合成する。
規約：三つの任意の実関手を保持。使われ方：BF 帰納段の Kan 性と前向き弱比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F L R : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (l : ∀ X, F.obj X ⟶ L.obj X) (r : ∀ X, F.obj X ⟶ R.obj X)
  (hl : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (l Y) =
    L.map X Y ≫ eHomWhiskerRight SSet (l X) (L.obj Y))
  (hr : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (r Y) =
    R.map X Y ≫ eHomWhiskerRight SSet (r X) (R.obj Y))

open SerrePositivity.SimplicialModel

/-- 同じ元の値は、元の実押し出しの Ex∞ Kan 複体。 -/
lemma pointedEnrichedCylinderCompletion_kanComplex (X : C) :
    KanComplex (((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 同じ実押し出しから Kan 値への元の単位は基礎 anodyne 射。 -/
lemma pointedEnrichedCylinderCompletionUnit_anodyne (X : C) :
    anodyneExtensions
      (show ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj ⟶
        ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
          pointedEnrichedCylinderCompletionUnit F L R l r hl hr X).right :=
  exInfinityPointedUnit_anodyne ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X)

/-- 元の同じ左標的から Kan 値への比較は基礎単射。 -/
lemma pointedEnrichedCylinderCompletionLeft_mono (X : C) :
    Mono (show (L.obj X).obj ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
        pointedEnrichedCylinderCompletionLeft F L R l r hl hr X).right := by
  let a : (L.obj X).obj ⟶
      ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderPushoutLeft F L R l r hl hr X
  let η : ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X
  let _ : Mono a.right := pointedEnrichedCylinderPushoutLeft_mono F L R l r hl hr X
  let _ : Mono η.right := Spectra.anodyne_mono _
    (pointedEnrichedCylinderCompletionUnit_anodyne F L R l r hl hr X)
  change Mono (a.right ≫ η.right)
  infer_instance

/-- 元の同じ右標的から Kan 値への比較は基礎単射。 -/
lemma pointedEnrichedCylinderCompletionRight_mono (X : C) :
    Mono (show (R.obj X).obj ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
        pointedEnrichedCylinderCompletionRight F L R l r hl hr X).right := by
  let a : (R.obj X).obj ⟶
      ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderPushoutRight F L R l r hl hr X
  let η : ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X
  let _ : Mono a.right := pointedEnrichedCylinderPushoutRight_mono F L R l r hl hr X
  let _ : Mono η.right := Spectra.anodyne_mono _
    (pointedEnrichedCylinderCompletionUnit_anodyne F L R l r hl hr X)
  change Mono (a.right ≫ η.right)
  infer_instance

/-- 左脚が局所化可逆なら、同じ Kan 値への右比較も局所化可逆。 -/
lemma pointedEnrichedCylinderCompletionRight_localized_isIso (X : C)
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map
      (show (F.obj X).obj ⟶ (L.obj X).obj from l X).right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show (R.obj X).obj ⟶
        ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
          pointedEnrichedCylinderCompletionRight F L R l r hl hr X).right) := by
  let a : (R.obj X).obj ⟶
      ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderPushoutRight F L R l r hl hr X
  let η : ((pointedEnrichedCylinderPushoutFunctor F L R l r hl hr).obj X).obj ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X
  let _ : IsIso (AnodyneHomotopy.anodyneQ.map a.right) :=
    pointedEnrichedCylinderPushoutRight_localized_isIso F L R l r hl hr X hX
  let _ : IsIso (AnodyneHomotopy.anodyneQ.map η.right) :=
    (Localization.inverts _ anodyneExtensions) _
      (pointedEnrichedCylinderCompletionUnit_anodyne F L R l r hl hr X)
  change IsIso (AnodyneHomotopy.anodyneQ.map (a.right ≫ η.right))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
