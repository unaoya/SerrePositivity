module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathEndpoints
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# forward 射列の pushout の始点の正規化

概要：元の pushout 射列の始点を指定対象へ移し、元の置換射を始点成分で回収する。
方針：Fin.cons の対象列と元の endpointIso を標準の Functor.copyObj へ代入する。
規約：元の pushout 対象の同型を使い、選択した対象そのものの等式は仮定しない。
使われ方：左右のブロックの共通対象を同じ元の分解の中間対象とする。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] {n : ℕ}

def normalizedPushoutObj (s : InitialReplacement C n) : Fin (n + 1) → C :=
  Fin.cons s.right (fun i => pushoutObj s i.succ)

lemma normalizedPushoutObj_zero (s : InitialReplacement C n) :
    normalizedPushoutObj s 0 = s.right := rfl

lemma normalizedPushoutObj_succ (s : InitialReplacement C n) (i : Fin n) :
    normalizedPushoutObj s i.succ = pushoutObj s i.succ := rfl

def normalizedPushoutObjIso (s : InitialReplacement C n) (i : Fin (n + 1)) :
    pushoutObj s i ≅ normalizedPushoutObj s i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (pushoutEndpointIso s).symm
  · exact Iso.refl _

lemma normalizedPushoutObjIso_zero (s : InitialReplacement C n) :
    normalizedPushoutObjIso s 0 = (pushoutEndpointIso s).symm := rfl

def normalizedPushoutPath (s : InitialReplacement C n) : ComposableArrows C n :=
  (pushoutPath s).copyObj (normalizedPushoutObj s) (normalizedPushoutObjIso s)

def pushoutNormalizationIso (s : InitialReplacement C n) :
    pushoutPath s ≅ normalizedPushoutPath s :=
  (pushoutPath s).isoCopyObj (normalizedPushoutObj s) (normalizedPushoutObjIso s)

def normalizedPushoutInclusion (s : InitialReplacement C n) :
    s.left ⟶ normalizedPushoutPath s := pushoutInclusion s ≫ (pushoutNormalizationIso s).hom

lemma normalizedPushoutInclusion_app (s : InitialReplacement C n) (i : Fin (n + 1)) :
    (normalizedPushoutInclusion s).app i =
      (pushoutInclusion s).app i ≫ (normalizedPushoutObjIso s i).hom := rfl

lemma normalizedPushoutInclusion_zero (s : InitialReplacement C n) :
    (normalizedPushoutInclusion s).app 0 = s.hom := by
  rw [normalizedPushoutInclusion_app, normalizedPushoutObjIso_zero]
  change (pushoutInclusion s).app 0 ≫ (pushoutEndpointIso s).inv = _
  rw [← pushoutEndpointIso_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.EInfinity.Hammock.ForwardPath
