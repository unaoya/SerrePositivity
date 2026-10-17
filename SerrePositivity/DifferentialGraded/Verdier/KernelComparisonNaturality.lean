module
public import SerrePositivity.DifferentialGraded.Verdier.KernelQuotientNaturality

/-! # kernel の全射に自然な完備商・局所 perfect 比較正方形 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

private lemma conjugatedComparison_naturality
    {H V T : Type*} [Category* H] [Category* V] [Category* T]
    (e : H ≌ V) (B : V ⥤ T) (L : H ⥤ T) (p : e.functor ⋙ B ≅ L)
    {X Y : V} (f : X ⟶ Y) :
    B.map f ≫ B.map (e.counitIso.inv.app Y) ≫ p.hom.app (e.inverse.obj Y) =
      B.map (e.counitIso.inv.app X) ≫ p.hom.app (e.inverse.obj X) ≫ L.map (e.inverse.map f) := by
  have h := congrArg (fun t => B.map t ≫ p.hom.app (e.inverse.obj Y))
    (e.counitIso.inv.naturality f)
  simp only [Functor.id_map, Functor.comp_map, CategoryTheory.Functor.map_comp,
    Category.assoc] at h
  have hp := p.hom.naturality (e.inverse.map f)
  simp only [Functor.comp_map] at hp
  rw [hp] at h
  exact h

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (E : Type w) [DGCategory A E] [Small.{u} E] (T : Set E)

/-- 指定完備 tria 商への実作用を、kernel の全射に対する関手として公開する。 -/
def supportedKernelCompletedTriaFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T) where
  obj K := mainKernelCompletedQuotientFunctor A D S E K.obj K.property.1 T K.property.2
  map f := whiskerLeft (perfectCompletedToTriaQuotientEquivalence A D S).inverse
    (whiskerRight ((supportedKernelCompletedFunctor A D E S T).map f)
      (perfectCompletedToTriaQuotientEquivalence A E T).functor)
  map_id K := by
    rw [CategoryTheory.Functor.map_id, whiskerRight_id']
    apply NatTrans.ext
    funext X
    rfl
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, whiskerRight_comp, whiskerLeft_comp]

variable (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 局所 perfect enhancement の H⁰ への実作用も、全 kernel 射を含む関手になる。 -/
def supportedKernelLocalPerfectFunctor :
    SupportedPerfectKernelCategory A D E S T ⥤
      (PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
        PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ) where
  obj K := mainKernelQuotientPerfectHomotopyFunctor A D S hD E K.obj K.property.1 T K.property.2 hE
  map f := whiskerLeft (localPerfectToPerfectVerdierEquivalence A D S hD).functor
    (whiskerRight ((supportedKernelCompletedFunctor A D E S T).map f)
      (localPerfectToPerfectVerdierEquivalence A E T hE).inverse)
  map_id K := by
    rw [CategoryTheory.Functor.map_id, whiskerRight_id']
    apply NatTrans.ext
    funext X
    rfl
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, whiskerRight_comp, whiskerLeft_comp]

/-- 既存の局所 perfect 正方形そのものを、kernel の全射に自然な族へ束ねる。 -/
def supportedKernelLocalPerfectSquare :
    supportedKernelCompletedTriaFunctor A D S E T ⋙
        (whiskeringLeft _ _ _).obj (localPerfectQuotientEquivalence A D S hD).functor ≅
      supportedKernelLocalPerfectFunctor A D S E T hD hE ⋙
        (whiskeringRight _ _ _).obj (localPerfectQuotientEquivalence A E T hE).functor :=
  NatIso.ofComponents
    (fun K => mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE)
    (by
      intro K L f
      apply NatTrans.ext
      funext X
      dsimp only [Functor.comp_map, whiskeringLeft_obj_map, whiskeringRight_obj_map,
        supportedKernelCompletedTriaFunctor, supportedKernelLocalPerfectFunctor,
        mainKernelLocalPerfectSquare, mainKernelPerfectVerdierSquare,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
        isoWhiskerRight_inv, isoWhiskerLeft_inv,
        NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_inv_app,
        associator_hom_app, rightUnitor_inv_app, rightUnitor_hom_app]
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      have h := conjugatedComparison_naturality
        (localPerfectToPerfectVerdierEquivalence A E T hE)
        (perfectCompletedToTriaQuotientEquivalence A E T).functor
        (localPerfectQuotientEquivalence A E T hE).functor
        (localPerfectVerdierFactors A E T hE)
        (((supportedKernelCompletedFunctor A D E S T).map f).app
          ((localPerfectToPerfectVerdierEquivalence A D S hD).functor.obj X))
      refine Eq.trans ?_ (h.trans ?_)
      · exact congrArg (fun z => (perfectCompletedToTriaQuotientEquivalence A E T).functor.map
          (((supportedKernelCompletedFunctor A D E S T).map f).app
            ((localPerfectToPerfectVerdierEquivalence A D S hD).functor.obj X)) ≫ z)
          (Category.id_comp _)
      · exact (Category.id_comp _).symm)

/-- 族の成分は、すでに公開した比較自然同型そのものである。 -/
lemma supportedKernelLocalPerfectSquare_app (K : SupportedPerfectKernelCategory A D E S T) :
    (supportedKernelLocalPerfectSquare A D S E T hD hE).app K =
      mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE := rfl

/-- kernel 射と元の局所 perfect 正方形を貼り合わせる、自然変換の等式。 -/
lemma supportedKernelLocalPerfectSquare_naturality
    {K L : SupportedPerfectKernelCategory A D E S T} (f : K ⟶ L) :
    whiskerLeft (localPerfectQuotientEquivalence A D S hD).functor
        ((supportedKernelCompletedTriaFunctor A D S E T).map f) ≫
        (mainKernelLocalPerfectSquare A D S hD E L.obj L.property.1 T L.property.2 hE).hom =
      (mainKernelLocalPerfectSquare A D S hD E K.obj K.property.1 T K.property.2 hE).hom ≫
        whiskerRight ((supportedKernelLocalPerfectFunctor A D S E T hD hE).map f)
          (localPerfectQuotientEquivalence A E T hE).functor :=
  (supportedKernelLocalPerfectSquare A D S E T hD hE).hom.naturality f
end DGQuotient
end SerrePositivity.DifferentialGraded
