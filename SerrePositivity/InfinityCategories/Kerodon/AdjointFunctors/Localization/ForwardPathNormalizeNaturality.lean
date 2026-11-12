module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathNormalizePullback
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathNormalizePushout

/-!
# 端点を正規化した forward ブロックの関手性

概要：指定された端点への移送は、動く端点と全縦射に自然である。
方針：元の comma 圏上の関手を標準の copyObj で移し、元の端点自然性を使う。
規約：正規化した終点の等式には eqToHom を明示する。
使われ方：同じ分解の中間対象を持つ左右ブロックの貼り合わせ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Pullback
variable [HasPullbacks C]

def normalizedPullbackFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n ⥤ ComposableArrows C n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackFunctor.copyObj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackPath _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackNormalizationIso

def normalizedPullbackFunctorIso :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n ⥤ _) ≅ normalizedPullbackFunctor :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackFunctor.isoCopyObj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackPath _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackNormalizationIso

def normalizedPullbackComparison {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackPath s ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackPath t := normalizedPullbackFunctor.map m

lemma normalizedPullbackComparison_app {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t)
    (i : Fin (n + 1)) :
    (normalizedPullbackComparison m).app i = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso s i).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparison m).app i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso t i).hom := rfl

lemma normalizedPullbackComparison_last {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t) :
    (normalizedPullbackComparison m).app (Fin.last n) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last s) ≫ m.left ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last t).symm := by
  rw [normalizedPullbackComparison_app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso_last,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso_last, Iso.trans_inv, Iso.trans_hom]
  change (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last s) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackEndpointIso s).inv) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparison m).app (Fin.last n) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackEndpointIso t).hom ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last t).symm = _
  simp only [Category.assoc]
  rw [← Category.assoc ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparison m).app (Fin.last n)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackEndpointIso_naturality, Category.assoc, Iso.inv_hom_id_assoc]

lemma normalizedPullbackProjection_naturality {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n}
    (m : s ⟶ t) :
    normalizedPullbackComparison m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s ≫ m.right := by
  apply NatTrans.ext
  funext i
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso s i).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparison m).app i ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso t i).hom) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso t i).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackProjection t).app i) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso s i).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackProjection s).app i) ≫ m.right.app i
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObjIso s i).inv ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pullbackComparisonApp_fst m i)

end Pullback

section Pushout
variable [HasPushouts C]

def normalizedPushoutFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n ⥤ ComposableArrows C n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFunctor.copyObj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutPath _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutNormalizationIso

def normalizedPushoutFunctorIso :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n ⥤ _) ≅ normalizedPushoutFunctor :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFunctor.isoCopyObj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutPath _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutNormalizationIso

def normalizedPushoutComparison {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutPath s ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutPath t := normalizedPushoutFunctor.map m

lemma normalizedPushoutComparison_app {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t)
    (i : Fin (n + 1)) :
    (normalizedPushoutComparison m).app i = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso s i).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparison m).app i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso t i).hom := rfl

lemma normalizedPushoutComparison_zero {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t) :
    (normalizedPushoutComparison m).app 0 = m.right := by
  rw [normalizedPushoutComparison_app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso_zero]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso s).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparison m).app 0 ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso t).inv = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutEndpointIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma normalizedPushoutInclusion_naturality {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n}
    (m : s ⟶ t) :
    m.left ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s ≫ normalizedPushoutComparison m := by
  apply NatTrans.ext
  funext i
  change m.left.app i ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion t).app i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso t i).hom) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutInclusion s).app i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso s i).hom) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso s i).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparison m).app i ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso t i).hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutObjIso t i).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutComparisonApp_inr m i).symm

end Pushout
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
