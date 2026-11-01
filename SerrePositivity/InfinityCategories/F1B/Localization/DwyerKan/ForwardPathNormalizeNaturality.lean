module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathNormalizePullback
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathNormalizePushout

/-!
# 端点を正規化した forward ブロックの関手性

概要：指定された端点への移送は、動く端点と全縦射に自然である。
方針：元の comma 圏上の関手を標準の copyObj で移し、元の端点自然性を使う。
規約：正規化した終点の等式には eqToHom を明示する。
使われ方：同じ分解の中間対象を持つ左右ブロックの貼り合わせ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {n : ℕ}

section Pullback
variable [HasPullbacks C]

def normalizedPullbackFunctor : TerminalReplacement C n ⥤ ComposableArrows C n :=
  pullbackFunctor.copyObj normalizedPullbackPath pullbackNormalizationIso

def normalizedPullbackFunctorIso :
    (pullbackFunctor : TerminalReplacement C n ⥤ _) ≅ normalizedPullbackFunctor :=
  pullbackFunctor.isoCopyObj normalizedPullbackPath pullbackNormalizationIso

def normalizedPullbackComparison {s t : TerminalReplacement C n} (m : s ⟶ t) :
    normalizedPullbackPath s ⟶ normalizedPullbackPath t := normalizedPullbackFunctor.map m

lemma normalizedPullbackComparison_app {s t : TerminalReplacement C n} (m : s ⟶ t)
    (i : Fin (n + 1)) :
    (normalizedPullbackComparison m).app i = (normalizedPullbackObjIso s i).inv ≫
      (pullbackComparison m).app i ≫ (normalizedPullbackObjIso t i).hom := rfl

lemma normalizedPullbackComparison_last {s t : TerminalReplacement C n} (m : s ⟶ t) :
    (normalizedPullbackComparison m).app (Fin.last n) =
      eqToHom (normalizedPullbackObj_last s) ≫ m.left ≫
        eqToHom (normalizedPullbackObj_last t).symm := by
  rw [normalizedPullbackComparison_app, normalizedPullbackObjIso_last,
    normalizedPullbackObjIso_last, Iso.trans_inv, Iso.trans_hom]
  change (eqToHom (normalizedPullbackObj_last s) ≫ (pullbackEndpointIso s).inv) ≫
      (pullbackComparison m).app (Fin.last n) ≫
        (pullbackEndpointIso t).hom ≫ eqToHom (normalizedPullbackObj_last t).symm = _
  simp only [Category.assoc]
  rw [← Category.assoc ((pullbackComparison m).app (Fin.last n)),
    pullbackEndpointIso_naturality, Category.assoc, Iso.inv_hom_id_assoc]

lemma normalizedPullbackProjection_naturality {s t : TerminalReplacement C n}
    (m : s ⟶ t) :
    normalizedPullbackComparison m ≫ normalizedPullbackProjection t =
      normalizedPullbackProjection s ≫ m.right := by
  apply NatTrans.ext
  funext i
  change ((normalizedPullbackObjIso s i).inv ≫ (pullbackComparison m).app i ≫
      (normalizedPullbackObjIso t i).hom) ≫
      ((normalizedPullbackObjIso t i).inv ≫ (pullbackProjection t).app i) =
    ((normalizedPullbackObjIso s i).inv ≫ (pullbackProjection s).app i) ≫ m.right.app i
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg ((normalizedPullbackObjIso s i).inv ≫ ·)
    (pullbackComparisonApp_fst m i)

end Pullback

section Pushout
variable [HasPushouts C]

def normalizedPushoutFunctor : InitialReplacement C n ⥤ ComposableArrows C n :=
  pushoutFunctor.copyObj normalizedPushoutPath pushoutNormalizationIso

def normalizedPushoutFunctorIso :
    (pushoutFunctor : InitialReplacement C n ⥤ _) ≅ normalizedPushoutFunctor :=
  pushoutFunctor.isoCopyObj normalizedPushoutPath pushoutNormalizationIso

def normalizedPushoutComparison {s t : InitialReplacement C n} (m : s ⟶ t) :
    normalizedPushoutPath s ⟶ normalizedPushoutPath t := normalizedPushoutFunctor.map m

lemma normalizedPushoutComparison_app {s t : InitialReplacement C n} (m : s ⟶ t)
    (i : Fin (n + 1)) :
    (normalizedPushoutComparison m).app i = (normalizedPushoutObjIso s i).inv ≫
      (pushoutComparison m).app i ≫ (normalizedPushoutObjIso t i).hom := rfl

lemma normalizedPushoutComparison_zero {s t : InitialReplacement C n} (m : s ⟶ t) :
    (normalizedPushoutComparison m).app 0 = m.right := by
  rw [normalizedPushoutComparison_app, normalizedPushoutObjIso_zero,
    normalizedPushoutObjIso_zero]
  change (pushoutEndpointIso s).hom ≫ (pushoutComparison m).app 0 ≫
    (pushoutEndpointIso t).inv = _
  rw [← Category.assoc, ← pushoutEndpointIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma normalizedPushoutInclusion_naturality {s t : InitialReplacement C n}
    (m : s ⟶ t) :
    m.left ≫ normalizedPushoutInclusion t =
      normalizedPushoutInclusion s ≫ normalizedPushoutComparison m := by
  apply NatTrans.ext
  funext i
  change m.left.app i ≫ ((pushoutInclusion t).app i ≫ (normalizedPushoutObjIso t i).hom) =
    ((pushoutInclusion s).app i ≫ (normalizedPushoutObjIso s i).hom) ≫
      ((normalizedPushoutObjIso s i).inv ≫ (pushoutComparison m).app i ≫
        (normalizedPushoutObjIso t i).hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (normalizedPushoutObjIso t i).hom)
    (pushoutComparisonApp_inr m i).symm

end Pushout
end SerrePositivity.EInfinity.Hammock.ForwardPath
