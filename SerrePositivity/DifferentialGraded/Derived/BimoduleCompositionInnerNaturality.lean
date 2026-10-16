module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPairNaturality

/-! # 合成された後因子の解像度比較の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w) (F : Type z)
  [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleComposeInnerMap (hF : localHomKFlat A F)
    {Q Q' : DerivedBimoduleCategory A C E} {R R' : DerivedBimoduleCategory A E F}
    (f : Q ⟶ Q') (g : R ⟶ R') :
    ((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q ⟶
      ((derivedBimoduleComposeFunctor A C E F hF).obj R').obj Q' :=
  ((derivedBimoduleComposeFunctor A C E F hF).obj R).map f ≫
    ((derivedBimoduleComposeFunctor A C E F hF).map g).app Q'

lemma derivedBimoduleComposeInnerResolutionIso_naturality
    (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    derivedBimoduleComposeInnerMap A C E F hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr).hom ≫
      (bimoduleToDerived A C F).map (composeMap A C E F s.hom t.hom) := by
  let iq := bimoduleDerivedIso A C E q hq
  let iq' := bimoduleDerivedIso A C E q' hq'
  have hs' : (bimoduleToDerived A C E).map f ≫ iq'.inv =
      iq.inv ≫ (bimoduleToDerived A C E).map s.hom := by
    apply (Iso.cancel_iso_hom_left iq _ _).1
    change (bimoduleToDerived A C E).map q ≫ _ = _
    rw [← Category.assoc, hs]
    change (_ ≫ iq'.hom) ≫ iq'.inv = iq.hom ≫ (iq.inv ≫ _)
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have ht' := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality
      A C E F hF T T' r r' hr hr' g t ht) ((bimoduleToDerived A C E).obj Q')
  simp only [NatTrans.comp_app] at ht'
  have hc := (derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).hom.naturality
    ((bimoduleToDerived A C E).map f)
  have hx := (derivedComposeWithMap A C E F T.property T'.property t.hom).naturality iq'.inv
  have hm : (derivedComposeWith A C E F T.obj T.property).map
        ((bimoduleToDerived A C E).map s.hom) ≫
      (derivedComposeWithMap A C E F T.property T'.property t.hom).app
        ((bimoduleToDerived A C E).obj S'.obj) =
      (bimoduleToDerived A C F).map (composeMap A C E F s.hom t.hom) := by
    rw [derivedComposeWith_map_base, derivedComposeWithMap_base_app,
      ← CategoryTheory.Functor.map_comp]
    congr 1
    have h := composeMap_comp A C E F s.hom (𝟙 S'.obj) (𝟙 T.obj) t.hom
    simpa only [Category.comp_id, Category.id_comp] using h.symm
  change (_ ≫ _) ≫
      ((derivedBimoduleComposeResolutionComputation A C E F hF R' T' r' hr').hom.app
          ((bimoduleToDerived A C E).obj Q') ≫
        (derivedComposeWith A C E F T'.obj T'.property).map iq'.inv) =
    ((derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).hom.app
        ((bimoduleToDerived A C E).obj Q) ≫
      (derivedComposeWith A C E F T.obj T.property).map iq.inv) ≫ _
  simp only [Category.assoc]
  rw [reassoc_of% ht']
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← hx]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hs', CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hm]

end SerrePositivity.DifferentialGraded.BimoduleTensor
