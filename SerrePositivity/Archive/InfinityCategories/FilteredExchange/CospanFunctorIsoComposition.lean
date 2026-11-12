module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：cospan の二脚の指定比較と可換同型の整合を二段の比較で合成する。
方針：前後合成の交換と指定同型の合成則。
規約：両段の指定値を保持。使われ方：全空間錐から元の引き戻し path への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二段の指定脚比較は元の可換同型に対して同時に整合する。
方針：二つの整合式を前合成と交換則で結ぶ。
規約：指定値の等式。使われ方：元の全空間の path との整合。 -/
lemma cospanFunctorIso_compose {W X A B C : SSet.{u}}
    (a : W ⟶ X) (p : A ⟶ C) (q : B ⟶ C)
    {ul : W ⟶ A} {ur : W ⟶ B} {vl fl : X ⟶ A} {vr fr : X ⟶ B}
    (el : FunctorIso ul (a ≫ vl)) (er : FunctorIso ur (a ≫ vr))
    (dl : FunctorIso vl fl) (dr : FunctorIso vr fr)
    (s : FunctorIso (ul ≫ p) (ur ≫ q)) (t : FunctorIso (vl ≫ p) (vr ≫ q))
    (h : FunctorIso (fl ≫ p) (fr ≫ q))
    (hs : s ≪≫ er.postcomp q = el.postcomp p ≪≫ t.precomp a)
    (ht : dl.postcomp p ≪≫ h = t ≪≫ dr.postcomp q) :
    (show FunctorIso ul (a ≫ fl) from el ≪≫ dl.precomp a).postcomp p ≪≫ h.precomp a =
      s ≪≫ (show FunctorIso ur (a ≫ fr) from er ≪≫ dr.precomp a).postcomp q := by
  have htp := congrArg (fun e : FunctorIso (vl ≫ p) (fr ≫ q) => e.precomp a) ht
  rw [functorIso_precomp_trans, functorIso_precomp_trans] at htp
  simp only [functorIso_postcomp_trans, functorIso_precomp_postcomp, Iso.trans_assoc]
  rw [htp, ← Iso.trans_assoc, ← hs, Iso.trans_assoc]

/-- 概要：二射影と path の終点を厳密な等式で移しても指定整合式を保つ。
方針：二終点の等式と指定値の型付き一致を消去する。
規約：元の比較同型を保持。使われ方：具体的な全空間射影への正規化。 -/
lemma cospanFunctorIso_target_transport {W A B C : SSet.{u}}
    {ul vl vl' : W ⟶ A} {ur vr vr' : W ⟶ B} (p : A ⟶ C) (q : B ⟶ C)
    (el : FunctorIso ul vl) (er : FunctorIso ur vr)
    (el' : FunctorIso ul vl') (er' : FunctorIso ur vr')
    (s : FunctorIso (ul ≫ p) (ur ≫ q))
    (h : FunctorIso (vl ≫ p) (vr ≫ q)) (h' : FunctorIso (vl' ≫ p) (vr' ≫ q))
    (hl : vl = vl') (hr : vr = vr') (hel : HEq el' el) (her : HEq er' er) (hh : HEq h' h)
    (hs : el.postcomp p ≪≫ h = s ≪≫ er.postcomp q) :
    el'.postcomp p ≪≫ h' = s ≪≫ er'.postcomp q := by
  subst vl' vr'
  cases eq_of_heq hel
  cases eq_of_heq her
  cases eq_of_heq hh
  exact hs

end SerrePositivity.InfinityCategories.F2
