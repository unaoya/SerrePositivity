module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarCompletionSquare
public import SerrePositivity.DifferentialGraded.Verdier.ScalarKaroubiShift
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiMapShift

/-! # 係数変更の完備化経路比較の shift 整合性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C C' P P' : Type*} [Category* C] [Category* C'] [Category* P] [Category* P']
  [HasShift C ℤ] [HasShift C' ℤ] [HasShift P ℤ] [HasShift P' ℤ]
  (e : C ≌ P) (e' : C' ≌ P') [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
  [e.CommShift ℤ] [e'.functor.CommShift ℤ] [e'.inverse.CommShift ℤ] [e'.CommShift ℤ]
  (F : C ⥤ C') (T : P ⥤ P') [F.CommShift ℤ] [T.CommShift ℤ]
  (α : F ⋙ e'.functor ≅ e.functor ⋙ T) [NatTrans.CommShift α.hom ℤ]

instance equivalenceInverseSquareCommShift :
    NatTrans.CommShift (equivalenceInverseSquare e e' F T α).hom ℤ := by
  let β : (e.inverse ⋙ F) ⋙ e'.functor ≅ (T ⋙ e'.inverse) ⋙ e'.functor :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso T ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft T e'.counitIso.symm ≪≫ (Functor.associator _ _ _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by
    dsimp only [β, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
    infer_instance
  refine NatTrans.CommShift.of_comp_faithful (G := e'.functor) (h := ?_)
  have he : whiskerRight (equivalenceInverseSquare e e' F T α).hom e'.functor = β.hom :=
    ((whiskeringRight _ _ _).obj e'.functor).map_preimage _
  rw [he]
  exact hβ
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S)

instance graphCompletedPerfectComparisonFunctorCommShift :
    (graphCompletedPerfectComparison A D S h).functor.CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance
instance graphCompletedPerfectComparisonInverseCommShift :
    (graphCompletedPerfectComparison A D S h).inverse.CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance
instance graphCompletedPerfectComparisonCommShift :
    (graphCompletedPerfectComparison A D S h).CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance

def localPerfectComparisonReassociate :
    (localPerfectQuotientEquivalence A D S h).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        (graphCompletedPerfectComparison A D S h).inverse :=
  Functor.associator _ _ _

instance localPerfectComparisonReassociateCommShift :
    NatTrans.CommShift (localPerfectComparisonReassociate A D S h).hom ℤ := by
  dsimp only [localPerfectComparisonReassociate]
  infer_instance

variable {A D} {A' : Type u} [CommRing A'] (φ : A →+* A')
  (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

instance scalarCompletedTriaSquareCommShift :
    NatTrans.CommShift (scalarCompletedTriaSquare φ D S h h').hom ℤ := by
  dsimp only [scalarCompletedTriaSquare]
  infer_instance

instance scalarCompletedPerfectSquareCommShift :
    NatTrans.CommShift (scalarCompletedPerfectSquare φ D S h h').hom ℤ := by
  dsimp only [scalarCompletedPerfectSquare, Iso.trans_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom]
  infer_instance

def scalarCompletedLocalPerfectCoherentSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ scalarCompletedTriaFunctor φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor :=
  isoWhiskerRight (localPerfectComparisonReassociate A D S h) _ ≪≫
    Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S h).inverse (scalarCompletedTriaFunctor φ D S h h') ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S h)
      (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h') _ _
      (scalarCompletedPerfectSquare φ D S h h')) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientScalarPerfectHomotopySquare φ D S).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      (localPerfectComparisonReassociate A' (ScalarExtension.DGBaseChange φ D) S h').symm

instance scalarCompletedLocalPerfectCoherentSquareCommShift :
    NatTrans.CommShift (scalarCompletedLocalPerfectCoherentSquare S h φ h').hom ℤ := by
  dsimp only [scalarCompletedLocalPerfectCoherentSquare, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance

lemma scalarCompletedLocalPerfectCoherentSquare_eq :
    scalarCompletedLocalPerfectCoherentSquare S h φ h' =
      scalarCompletedLocalPerfectSquare φ D S h h' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  dsimp only [scalarCompletedLocalPerfectCoherentSquare, scalarCompletedLocalPerfectSquare,
    localPerfectComparisonReassociate, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app]
  let H := (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
  let a := (equivalenceInverseSquare
    (graphCompletedPerfectComparison A D S h)
    (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h') _ _
    (scalarCompletedPerfectSquare φ D S h h')).hom.app (H.obj X)
  let b := (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h').inverse.map
    ((quotientScalarPerfectHomotopySquare φ D S).inv.app X)
  let Y := (graphCompletedPerfectComparison A D S h).inverse.obj (H.obj X)
  exact (show (scalarCompletedTriaFunctor φ D S h h').map (𝟙 Y) ≫
      𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ from by
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Category.comp_id])

instance scalarCompletedLocalPerfectSquareCommShift :
    NatTrans.CommShift (scalarCompletedLocalPerfectSquare φ D S h h').hom ℤ := by
  rw [← scalarCompletedLocalPerfectCoherentSquare_eq S h φ h']
  infer_instance

instance scalarCompletionComparisonIsoCommShift :
    NatTrans.CommShift (scalarCompletionComparisonIso φ D S h h').hom ℤ := by
  let L := (localPerfectQuotientEquivalence A D S h).functor
  let ff := (localPerfectQuotientEquivalence A D S h).congrLeft
    (E := CompletedTriaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
  let : ff.inverse.Faithful := inferInstance
  refine natTransCommShift_of_precomp L _ (hτ := ?_)
  have he : whiskerLeft L (scalarCompletionComparisonIso φ D S h h').hom =
      (scalarCompletedLocalPerfectSquare φ D S h h' ≪≫
        (localPerfectScalarExtensionSquare φ D S h h').symm).hom := ff.inverse.map_preimage _
  rw [he]
  dsimp only [Iso.trans_hom]
  infer_instance

def scalarCompletionComparisonTriangle :=
  Functor.mapTriangleIso (scalarCompletionComparisonIso φ D S h h')

instance scalarCompletionToKaroubiSquareCommShift :
    NatTrans.CommShift (scalarCompletionToKaroubiSquare φ D S h h').hom ℤ := by
  let : NatTrans.CommShift
      (show toKaroubi (TriaQuotient A D S) ⋙ scalarCompletedTriaFunctor φ D S h h' ⟶
        localScalarTriaExtension φ S h h' ⋙
          toKaroubi (TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S) from
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
          (localScalarTriaExtension φ S h h')).hom) ℤ :=
    karoubiFactorCommShift (localScalarTriaExtension φ S h h')
  dsimp only [scalarCompletionToKaroubiSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

def scalarCompletionToKaroubiSquareTriangle :=
  Functor.mapTriangleIso (scalarCompletionToKaroubiSquare φ D S h h')
end DGQuotient
end SerrePositivity.DifferentialGraded
