module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingMonadLaws
public import SerrePositivity.InfinityCategories.HA.Monads.NativeMonad
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
概要：walking monad の単体的豊穣圏と、全作用の豊穣関手による表示。
方針：唯一の対象の自己 Hom をN(Δ₊)とし、順序和の全法則から構成する。
規約：豊穣 Hom は全単体集合。h Fun 上の通常のモナドとは区別する。
使われ方：HA §4.7.2–§4.7.3・Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。
Kerodon Remark 6.2.1.4（Tag 02EN）への忘却に先立つ全coherenceの表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking monad の唯一の対象。
方針：一元の型を取る。規約：Homの宇宙とは独立。
使われ方：HA §4.7.2、Riehl–Verity Remark 3.3.8 のwalking monad。 -/
inductive WalkingMonadObject where
  /-- モナドが作用する唯一の対象。 -/
  | star

/-- 概要：順序和を合成とする実際の単体的豊穣walking monad。
方針：指定の内部モノイドの全単位・結合則を使う。
規約：存在をinstance引数として仮定しない。
使われ方：HA §4.7.2–§4.7.3 の全モナドの豊穣表示。 -/
instance walkingMonadEnrichedCategory : EnrichedCategory SSet.{u} WalkingMonadObject where
  Hom _ _ := WalkingMonadShape
  id _ := walkingMonadUnit
  comp _ _ _ := walkingMonadComposition
  id_comp _ _ := by
    let := walkingMonadMonObj.{u}
    change (λ_ WalkingMonadShape.{u}).inv ≫
      (MonObj.one (X := WalkingMonadShape.{u}) ▷ WalkingMonadShape.{u}) ≫
        MonObj.mul = _
    rw [MonObj.one_mul, Iso.inv_hom_id]
  comp_id _ _ := by
    let := walkingMonadMonObj.{u}
    change (ρ_ WalkingMonadShape.{u}).inv ≫
      (WalkingMonadShape.{u} ◁ MonObj.one (X := WalkingMonadShape.{u})) ≫
        MonObj.mul = _
    rw [MonObj.mul_one, Iso.inv_hom_id]
  assoc _ _ _ _ := by
    let := walkingMonadMonObj.{u}
    change (α_ WalkingMonadShape.{u} WalkingMonadShape.{u} WalkingMonadShape.{u}).inv ≫
      (MonObj.mul (X := WalkingMonadShape.{u}) ▷ WalkingMonadShape.{u}) ≫
        MonObj.mul = _
    rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
    rfl

/-- 概要：値域の閉自己豊穣構造を固定する。方針：既存の構成を使う。
規約：全内部Homの合成。使われ方：HA §4.7.2、Kerodon Remark 6.2.1.4（Tag 02EN）。 -/
local instance endofunctorClosedEnrichment : EnrichedCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedCategorySelf SSet.{u}

namespace NativeMonad

variable {C : SSet.{u}}

/-- 概要：全モナド作用をwalking monadからの豊穣関手として表示する。
方針：唯一の対象をC、全Homの写像を元のactionとする。
規約：元の全作用・単位・積を保持する。
使われ方：HA Proposition 4.7.3.3 の全coherentなモナドの受け渡し。 -/
def toEnrichedFunctor (T : NativeMonad C) :
    EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u} where
  obj _ := C
  map _ _ := T.action
  map_id _ := T.map_unit
  map_comp _ _ _ := by
    change walkingMonadComposition ≫ T.action =
      (T.action ⊗ₘ T.action) ≫ endofunctorComposition C
    exact T.map_composition

/-- 概要：walking monadの豊穣関手から同じ台の全モナド作用を戻す。
方針：唯一の対象とその全Homの写像を取り、関手の法則を使う。
規約：対象のホモトピー同値への移送はしない。
使われ方：HA §4.7.2–§4.7.3 のwalking monad表示の照合。 -/
def ofEnrichedFunctor
    (F : EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}) :
    NativeMonad (F.obj .star) where
  action := F.map .star .star
  map_unit := F.map_id .star
  map_composition := by
    exact F.map_comp .star .star .star

/-- 概要：豊穣表示から戻しても元の全モナド作用は変わらない。
方針：actionの外延性を使う。規約：同じCの上で比較する。
使われ方：HA §4.7.2 の表示による情報の保存。 -/
lemma of_toEnrichedFunctor (T : NativeMonad C) :
    ofEnrichedFunctor T.toEnrichedFunctor = T := by
  apply NativeMonad.ext
  rfl

/-- 概要：戻した全作用の豊穣関手は元の豊穣関手に一致する。
方針：唯一の対象での外延性。規約：全Hom写像の等式として保持する。
使われ方：HA §4.7.2 の同じcoherentな表示の検収。 -/
lemma to_ofEnrichedFunctor (F : EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}) :
    (ofEnrichedFunctor F).toEnrichedFunctor = F := by
  exact EnrichedFunctor.ext SSet.{u} (fun x => by cases x; rfl)
    (fun x y => by cases x; cases y; simp only [eqToHom_refl, Category.comp_id]; rfl)

end NativeMonad

end SerrePositivity.InfinityCategories.HA.Monads
