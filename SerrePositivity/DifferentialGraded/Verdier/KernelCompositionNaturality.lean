module
public import SerrePositivity.DifferentialGraded.Verdier.KernelCompositionComparison
public import SerrePositivity.DifferentialGraded.Verdier.HorizontalComparison

/-! # 降下した実際の kernel 合成比較の両 kernel 射に関する自然性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P P' : SupportedPerfectKernelCategory A D E S T)
  (Q Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q')

/-- 許容 kernel の合成射は U16 の実際の主導来合成射。 -/
def supportedKernelCompositionMap :
    supportedKernelComposite A D E B S T U hD P Q ⟶
      supportedKernelComposite A D E B S T U hD P' Q' :=
  ObjectProperty.homMk (kernelComposeMap A D E B hD f.hom g.hom)

/-- 元の Perf 上に前合成した合成因子化は、kernel 射の水平合成に自然。 -/
lemma supportedKernelVerdierCompositeFactors_naturality :
    whiskerLeft (perfectVerdierQuotient A D S)
        (NatTrans.hcomp ((supportedKernelVerdierFunctor A D E S T).map f)
          ((supportedKernelVerdierFunctor A E B T U).map g)) ≫
        (supportedKernelVerdierCompositeFactors A D E B S T U P' Q').hom =
      (supportedKernelVerdierCompositeFactors A D E B S T U P Q).hom ≫
        whiskerRight (NatTrans.hcomp ((supportedKernelPerfectFunctor A D E S T).map f)
          ((supportedKernelPerfectFunctor A E B T U).map g)) (perfectVerdierQuotient A B U) :=
  horizontalComparison_naturality
    (perfectVerdierQuotient A D S) (perfectVerdierQuotient A E T) (perfectVerdierQuotient A B U)
    (perfectKernelVerdierSquare A D E P.obj P.property.1 S T P.property.2)
    (perfectKernelVerdierSquare A D E P'.obj P'.property.1 S T P'.property.2)
    (perfectKernelVerdierSquare A E B Q.obj Q.property.1 T U Q.property.2)
    (perfectKernelVerdierSquare A E B Q'.obj Q'.property.1 T U Q'.property.2)
    _ _ _ _ ((supportedKernelVerdierFactors A D E S T).hom.naturality f)
    ((supportedKernelVerdierFactors A E B T U).hom.naturality g)

/-- 実際に局所化した合成比較そのものは、両 kernel の任意の主導来射に自然。 -/
lemma supportedKernelVerdierCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelVerdierFunctor A D E S T).map f)
        ((supportedKernelVerdierFunctor A E B T U).map g) ≫
        (supportedKernelVerdierCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelVerdierCompositionIso A D E B S T U hD P Q).hom ≫
        supportedKernelVerdierMap A D B S U
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) := by
  apply Localization.natTrans_ext (perfectVerdierQuotient A D S) (perfectNullObjects A D S).trW
  intro X
  simp only [NatTrans.comp_app, supportedKernelVerdierCompositionIso_app]
  let C := supportedKernelComposite A D E B S T U hD P Q
  let C' := supportedKernelComposite A D E B S T U hD P' Q'
  let fc := supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g
  have ha := NatTrans.congr_app
    (supportedKernelVerdierCompositeFactors_naturality A D E B S T U P P' Q Q' f g) X
  have hb := NatTrans.congr_app ((supportedKernelVerdierFactors A D B S U).hom.naturality fc) X
  have he := congrArg (perfectVerdierQuotient A B U).map
    (NatTrans.congr_app
      (supportedKernelPerfectCompositionIso_naturality A D E B S T U hD P Q P' Q' f g) X)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at ha hb
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp] at he
  have h := transportedComparison_naturality
    ((supportedKernelVerdierCompositeFactors A D E B S T U P Q).app X)
    ((supportedKernelVerdierCompositeFactors A D E B S T U P' Q').app X)
    (((supportedKernelVerdierFactors A D B S U).app C).app X)
    (((supportedKernelVerdierFactors A D B S U).app C').app X)
    ((perfectVerdierQuotient A B U).mapIso
      ((supportedKernelPerfectCompositionIso A D E B S T U hD P Q).app X))
    ((perfectVerdierQuotient A B U).mapIso
      ((supportedKernelPerfectCompositionIso A D E B S T U hD P' Q').app X))
    _ _ _ _ ha hb he
  dsimp only [C, C', fc, supportedKernelVerdierFactors, supportedKernelVerdierFunctor] at h ⊢
  simpa only [Category.assoc, NatTrans.hcomp_app, NatIso.ofComponents.app,
    Iso.app_hom, Iso.app_inv, mapIso_hom, Functor.comp_map, Functor.comp_obj,
    Functor.whiskeringLeft_obj_map, Functor.whiskeringLeft_obj_obj, whiskerLeft_app] using h

section Karoubi
variable {C V W : Type*} [Category* C] [Category* V] [Category* W]
  {F F' : C ⥤ V} {G G' : V ⥤ W} (α : F ⟶ F') (β : G ⟶ G')

/-- Karoubi 延長の既存の合成比較も、両関手の自然変換に自然。 -/
lemma karoubiFunctorCompositionIso_naturality :
    NatTrans.hcomp ((functorExtension₂ C V).map α) ((functorExtension₂ V W).map β) ≫
        (karoubiFunctorCompositionIso F' G').hom =
      (karoubiFunctorCompositionIso F G).hom ≫
        (functorExtension₂ C W).map (NatTrans.hcomp α β) := by
  apply (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi W)).map_injective
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [whiskeringLeft_obj_map, whiskerLeft_app,
    NatTrans.hcomp_app, karoubiFunctorCompositionIso, Iso.refl_hom,
    Karoubi.comp_f, functorExtension₂_obj_map_f, functorExtension₂_map_app_f,
    functorExtension₂_obj_obj_p, toKaroubi_obj_X, toKaroubi_obj_p,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  change (β.app (F.obj X) ≫ G'.map (𝟙 (F.obj X))) ≫ G'.map (α.app X) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
end Karoubi

/-- 完備化後の実際の合成比較も、両 kernel の任意の主導来射に自然。 -/
lemma supportedKernelCompletedCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelCompletedFunctor A D E S T).map f)
        ((supportedKernelCompletedFunctor A E B T U).map g) ≫
        (supportedKernelCompletedCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelCompletedCompositionIso A D E B S T U hD P Q).hom ≫
        (supportedKernelCompletedFunctor A D B S U).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) := by
  simp only [supportedKernelCompletedCompositionIso, Iso.trans_hom, mapIso_hom]
  change NatTrans.hcomp
      ((functorExtension₂ _ _).map ((supportedKernelVerdierFunctor A D E S T).map f))
      ((functorExtension₂ _ _).map ((supportedKernelVerdierFunctor A E B T U).map g)) ≫ _ = _
  rw [← Category.assoc, karoubiFunctorCompositionIso_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, supportedKernelVerdierCompositionIso_naturality,
    CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm
end SerrePositivity.DifferentialGraded
