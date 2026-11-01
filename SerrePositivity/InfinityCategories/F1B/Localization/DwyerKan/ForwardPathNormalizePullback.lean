module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathEndpoints
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# forward 射列の pullback の終点の正規化

概要：元の pullback 射列の終点を指定対象へ移し、元の置換射を終点成分で回収する。
方針：Fin.snoc の対象列と元の endpointIso を標準の Functor.copyObj へ代入する。
規約：選択した pullback 対象との同型と、正規化後の終点の等式を区別する。
使われ方：同じ中間対象で左右の forward ブロックを貼り合わせる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {n : ℕ}

def normalizedPullbackObj (s : TerminalReplacement C n) : Fin (n + 1) → C :=
  Fin.snoc (fun i => pullbackObj s i.castSucc) s.left

lemma normalizedPullbackObj_last (s : TerminalReplacement C n) :
    normalizedPullbackObj s (Fin.last n) = s.left := Fin.snoc_last _ _

lemma normalizedPullbackObj_castSucc (s : TerminalReplacement C n) (i : Fin n) :
    normalizedPullbackObj s i.castSucc = pullbackObj s i.castSucc := Fin.snoc_castSucc _ _ _

def normalizedPullbackObjIso (s : TerminalReplacement C n) (i : Fin (n + 1)) :
    pullbackObj s i ≅ normalizedPullbackObj s i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact pullbackEndpointIso s ≪≫ eqToIso (normalizedPullbackObj_last s).symm
  · exact eqToIso (normalizedPullbackObj_castSucc s j).symm

lemma normalizedPullbackObjIso_last (s : TerminalReplacement C n) :
    normalizedPullbackObjIso s (Fin.last n) =
      pullbackEndpointIso s ≪≫ eqToIso (normalizedPullbackObj_last s).symm := by
  simp only [normalizedPullbackObjIso, Fin.lastCases_last]

def normalizedPullbackPath (s : TerminalReplacement C n) : ComposableArrows C n :=
  (pullbackPath s).copyObj (normalizedPullbackObj s) (normalizedPullbackObjIso s)

def pullbackNormalizationIso (s : TerminalReplacement C n) :
    pullbackPath s ≅ normalizedPullbackPath s :=
  (pullbackPath s).isoCopyObj (normalizedPullbackObj s) (normalizedPullbackObjIso s)

def normalizedPullbackProjection (s : TerminalReplacement C n) :
    normalizedPullbackPath s ⟶ s.right := (pullbackNormalizationIso s).inv ≫ pullbackProjection s

lemma normalizedPullbackProjection_app (s : TerminalReplacement C n) (i : Fin (n + 1)) :
    (normalizedPullbackProjection s).app i =
      (normalizedPullbackObjIso s i).inv ≫ (pullbackProjection s).app i := rfl

lemma normalizedPullbackProjection_last (s : TerminalReplacement C n) :
    (normalizedPullbackProjection s).app (Fin.last n) =
      eqToHom (normalizedPullbackObj_last s) ≫ s.hom := by
  rw [normalizedPullbackProjection_app, normalizedPullbackObjIso_last, Iso.trans_inv]
  change (eqToHom (normalizedPullbackObj_last s) ≫ (pullbackEndpointIso s).inv) ≫
    (pullbackProjection s).app (Fin.last n) = _
  rw [← pullbackEndpointIso_fac, Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.EInfinity.Hammock.ForwardPath
