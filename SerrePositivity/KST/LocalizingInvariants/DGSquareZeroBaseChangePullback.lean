module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeLift
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal

/-!
概要：底を制限した平方零代数を、元の底射と射影の実 pullback の頂点にする。
方針：構成した厳密な底変更 lift と、底・係数の二射影で普遍性を証明する。
規約：元の底変更射と底射影を保持。使われ方：相対経路の共通底への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)

lemma baseChange_hom_ext {s t : W ⟶ algebra A (bimoduleRestrict q N)}
    (hp : s ≫ projection A (bimoduleRestrict q N) = t ≫ projection A (bimoduleRestrict q N))
    (hm : s ≫ baseChangeMap q N = t ≫ baseChangeMap q N) : s = t := by
  apply Mon.Hom.ext
  apply biprod.hom_ext
  · exact congrArg Mon.Hom.hom hp
  · have he : s.hom ≫ biprod.map q.hom (𝟙 N.X) = t.hom ≫ biprod.map q.hom (𝟙 N.X) :=
      congrArg Mon.Hom.hom hm
    let s' : W.X ⟶ A.X ⊞ N.X := s.hom
    let t' : W.X ⟶ A.X ⊞ N.X := t.hom
    have he' : s' ≫ biprod.map q.hom (𝟙 N.X) = t' ≫ biprod.map q.hom (𝟙 N.X) := he
    have hs := congrArg (fun z => z ≫ (biprod.snd : B.X ⊞ N.X ⟶ N.X)) he'
    have ht : s' ≫ biprod.snd = t' ≫ biprod.snd := by
      simpa only [Category.assoc, biprod.map_snd, Category.comp_id] using hs
    exact ht

def baseChangeCone : PullbackCone q (projection B N) :=
  PullbackCone.mk (projection A (bimoduleRestrict q N)) (baseChangeMap q N)
    (baseChangeMap_projection q N).symm

def baseChange_isLimit : IsLimit (baseChangeCone q N) :=
  PullbackCone.IsLimit.mk (baseChangeMap_projection q N).symm
    (fun s => baseChangeLift q N s.fst s.snd s.condition.symm)
    (fun s => baseChangeLift_projection q N s.fst s.snd s.condition.symm)
    (fun s => baseChangeLift_map q N s.fst s.snd s.condition.symm)
    (fun s m hp hm => baseChange_hom_ext q N
      (hp.trans (baseChangeLift_projection q N s.fst s.snd s.condition.symm).symm)
      (hm.trans (baseChangeLift_map q N s.fst s.snd s.condition.symm).symm))

def baseChangeIso : algebra A (bimoduleRestrict q N) ≅ MonoidPullback.obj q (projection B N) :=
  (baseChange_isLimit q N).conePointUniqueUpToIso (MonoidPullback.isLimit _ _)

lemma baseChangeIso_projection : (baseChangeIso q N).hom ≫
    MonoidPullback.fst q (projection B N) = projection A (bimoduleRestrict q N) :=
  (baseChange_isLimit q N).conePointUniqueUpToIso_hom_comp
    (MonoidPullback.isLimit _ _) WalkingCospan.left

lemma baseChangeIso_map : (baseChangeIso q N).hom ≫ MonoidPullback.snd q (projection B N) =
    baseChangeMap q N := (baseChange_isLimit q N).conePointUniqueUpToIso_hom_comp
      (MonoidPullback.isLimit _ _) WalkingCospan.right

end SerrePositivity.KST.LocalizingInvariants.SquareZero
