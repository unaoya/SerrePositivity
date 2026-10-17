module
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Shift.Quotient

/-! # 忠実な前合成による自然変換のshift整合性の検出 -/
@[expose] public section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

lemma natTransCommShift_of_faithful_precomp (S : Type*) [AddMonoid S]
    {C K T : Type*} [Category* C] [Category* K] [Category* T]
    [HasShift C S] [HasShift K S] [HasShift T S]
    (Q : C ⥤ K) [((Functor.whiskeringLeft C K T).obj Q).Faithful] [Q.CommShift S]
    {F G : K ⥤ T} [F.CommShift S] [G.CommShift S] (τ : F ⟶ G)
    (hτ : NatTrans.CommShift (Functor.whiskerLeft Q τ) S) : NatTrans.CommShift τ S where
  shift_comm s := by
    let := hτ
    apply ((Functor.whiskeringLeft C K T).obj Q).map_injective
    apply NatTrans.ext
    funext X
    rw [← cancel_epi (F.map ((Q.commShiftIso s).hom.app X))]
    have h := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ) s X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Category.assoc] at h
    rw [← τ.naturality_assoc] at h
    exact h

lemma quotientNatIsoLift_commShift (S : Type*) [AddMonoid S]
    {C T : Type*} [Category* C] [Category* T] [HasShift C S] [HasShift T S]
    (r : HomRel C) [r.IsCompatibleWithShift S]
    {F G : CategoryTheory.Quotient r ⥤ T} [F.CommShift S] [G.CommShift S]
    (e : CategoryTheory.Quotient.functor r ⋙ F ≅ CategoryTheory.Quotient.functor r ⋙ G)
    (he : NatTrans.CommShift e.hom S) :
    NatTrans.CommShift (CategoryTheory.Quotient.natIsoLift r e).hom S := by
  apply natTransCommShift_of_faithful_precomp S (CategoryTheory.Quotient.functor r)
  change NatTrans.CommShift e.hom S
  exact he

end SerrePositivity.DifferentialGraded
