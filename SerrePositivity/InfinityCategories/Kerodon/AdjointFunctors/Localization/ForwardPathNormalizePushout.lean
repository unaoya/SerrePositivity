module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathEndpoints
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# forward 射列の pushout の始点の正規化

概要：元の pushout 射列の始点を指定対象へ移し、元の置換射を始点成分で回収する。
方針：Fin.cons の対象列と元の endpointIso を標準の Functor.copyObj へ代入する。
規約：元の pushout 対象の同型を使い、選択した対象そのものの等式は仮定しない。
使われ方：左右のブロックの共通対象を同じ元の分解の中間対象とする。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] {n : ℕ}

def normalizedPushoutObj (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) : Fin (n + 1) → C :=
  Fin.cons s.right (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutObj s i.succ)

lemma normalizedPushoutObj_zero (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    normalizedPushoutObj s 0 = s.right := rfl

lemma normalizedPushoutObj_succ (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) (i : Fin n) :
    normalizedPushoutObj s i.succ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutObj s i.succ := rfl

def normalizedPushoutObjIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutObj s i ≅ normalizedPushoutObj s i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso s).symm
  · exact Iso.refl _

lemma normalizedPushoutObjIso_zero (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    normalizedPushoutObjIso s 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso s).symm := rfl

def normalizedPushoutPath (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) : ComposableArrows C n :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath s).copyObj (normalizedPushoutObj s) (normalizedPushoutObjIso s)

def pushoutNormalizationIso (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath s ≅ normalizedPushoutPath s :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath s).isoCopyObj (normalizedPushoutObj s) (normalizedPushoutObjIso s)

def normalizedPushoutInclusion (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    s.left ⟶ normalizedPushoutPath s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion s ≫ (pushoutNormalizationIso s).hom

lemma normalizedPushoutInclusion_app (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) (i : Fin (n + 1)) :
    (normalizedPushoutInclusion s).app i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion s).app i ≫ (normalizedPushoutObjIso s i).hom := rfl

lemma normalizedPushoutInclusion_zero (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    (normalizedPushoutInclusion s).app 0 = s.hom := by
  rw [normalizedPushoutInclusion_app, normalizedPushoutObjIso_zero]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion s).app 0 ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso s).inv = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
