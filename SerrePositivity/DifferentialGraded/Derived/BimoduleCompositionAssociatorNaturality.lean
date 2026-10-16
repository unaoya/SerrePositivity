module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionInnerNaturality
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorResolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorNaturality

/-! # 解像度比較に関する全導来結合比較の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleComposeNestedResolutionIso_naturality
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
    (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) ≫
      (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom ≫
      derivedComposeWithMap A B C F
        (rightKFlatCompose A C E F S T).property (rightKFlatCompose A C E F S' T').property
        (composeMap A C E F s.hom t.hom) := by
  have h := derivedBimoduleComposeInnerResolutionIso_naturality
    A C E F hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C F hF
    (show rightKFlatCompose A C E F S T ⟶ rightKFlatCompose A C E F S' T' from
      ⟨composeMap A C E F s.hom t.hom⟩)
  change _ ≫ ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q' R' S' T' q' r' hq' hr').hom ≫ _) =
    ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr).hom ≫ _) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc, hk, ← Category.assoc]

lemma derivedBimoduleAssociatorResolutionIso_naturality
    (hE : localHomKFlat A E) (hF : localHomKFlat A F)
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
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) := by
  have hp := derivedBimoduleComposePairResolutionIso_naturality
    A B C E F hE hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have hn := derivedBimoduleComposeNestedResolutionIso_naturality
    A B C E F hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have ha := derivedAssociatorIso_naturality A B C E F
    S.property S'.property T.property T'.property s.hom t.hom
  change _ ≫ (rightKFlatDerivedAssociator A B C E F S' T').hom =
    (rightKFlatDerivedAssociator A B C E F S T).hom ≫ _ at ha
  apply (Iso.cancel_iso_hom_right _ _
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q' R' S' T' q' r' hq' hr')).1
  simp only [Category.assoc]
  rw [derivedBimoduleAssociatorResolutionIso_fac]
  rw [← Category.assoc, hp]
  simp only [Category.assoc] at ha ⊢
  rw [ha]
  rw [hn]
  simp only [← Category.assoc]
  rw [derivedBimoduleAssociatorResolutionIso_fac]

lemma derivedBimoduleAssociatorBaseIso_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q Q' : BimoduleCategory A C E}
    {R R' : BimoduleCategory A E F} (f : Q ⟶ Q') (g : R ⟶ R') :
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q' R').hom =
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) := by
  apply derivedBimoduleAssociatorResolutionIso_naturality A B C E F hE hF
    (rightKFlatResolutionObj A C E hE Q) (rightKFlatResolutionObj A C E hE Q')
    (rightKFlatResolutionObj A E F hF R) (rightKFlatResolutionObj A E F hF R')
    _ _ _ _ _ _ _ _ f g
    (rightKFlatReplacementMap A C E hE f) (rightKFlatReplacementMap A E F hF g)
  · have h := rightKFlatGlobalAugmentation_naturality A C E hE f
    change (rightKFlatDerivedInclusion A C E).map
      ((rightKFlatToDerived A C E).map (rightKFlatReplacementMap A C E hE f)) ≫ _ = _ at h
    rw [rightKFlatDerivedInclusion_map_base] at h
    exact h.symm
  · have h := rightKFlatGlobalAugmentation_naturality A E F hF g
    change (rightKFlatDerivedInclusion A E F).map
      ((rightKFlatToDerived A E F).map (rightKFlatReplacementMap A E F hF g)) ≫ _ = _ at h
    rw [rightKFlatDerivedInclusion_map_base] at h
    exact h.symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
