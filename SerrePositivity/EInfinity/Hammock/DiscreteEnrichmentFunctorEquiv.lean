module

public import SerrePositivity.EInfinity.Hammock.DiscreteEnrichmentLift

/-!
# 元の離散豊穣圏からの関手と通常の underlying 圏への関手の同値

概要：元の射の一定単体による移送と離散豊穣化は互いに逆である。
方針：元の対象・全射と一定単体上の外延性を使う。
規約：元の対象写像と各 Hom の単体写像を保持する。
使われ方：非指定自由部分からの豊穣関手を生成矢の像へ移す。
-/

@[expose] public section
universe u v uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.DiscreteEnrichment
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [EnrichedCategory SSet.{v} D]

lemma ordinary_lift (K : C ⥤ ForgetEnrichment SSet.{v} D) :
    ordinaryFunctor (liftFunctor K) = K := by
  apply CategoryTheory.Functor.hext (F := ordinaryFunctor (liftFunctor K)) (G := K) (fun _ => rfl)
  intro X Y f
  change HEq (ForgetEnrichment.homOf SSet.{v} (point f ≫ liftMap K X Y)) (K.map f)
  rw [liftMap_point]
  rfl

lemma lift_ordinary :
    letI := enrichedCategory (C := C)
    ∀ F : EnrichedFunctor SSet.{v} C D, liftFunctor (ordinaryFunctor F) = F := by
  let := enrichedCategory (C := C)
  intro F
  apply EnrichedFunctor.ext SSet.{v} (F := liftFunctor (ordinaryFunctor F)) (G := F) (fun _ => rfl)
  intro X Y
  have he : liftMap (ordinaryFunctor F) X Y = F.map X Y := by
    apply point_ext
    intro f
    exact liftMap_point (ordinaryFunctor F) f
  change liftMap (ordinaryFunctor F) X Y ≫ 𝟙 (F.obj X ⟶[SSet.{v}] F.obj Y) = F.map X Y
  exact (Category.comp_id (liftMap (ordinaryFunctor F) X Y)).trans he

def functorEquiv :
    letI := enrichedCategory (C := C)
    EnrichedFunctor SSet.{v} C D ≃ (C ⥤ ForgetEnrichment SSet.{v} D) := by
  letI := enrichedCategory (C := C)
  exact
    { toFun := ordinaryFunctor
      invFun := liftFunctor
      left_inv := lift_ordinary
      right_inv := ordinary_lift }

end SerrePositivity.EInfinity.Hammock.DiscreteEnrichment
