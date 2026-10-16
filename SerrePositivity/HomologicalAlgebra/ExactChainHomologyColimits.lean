module
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits

/-! # Exact colimits of arbitrary shapes and actual chain homology cocones -/
@[expose] public noncomputable section
universe v u w t
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type w} [Category.{t} J]

/-- Transpose a chain diagram into a chain complex of diagrams. -/
def chainDiagramComplex (F : J ⥤ ChainComplex C ℕ) :
    ChainComplex (J ⥤ C) ℕ where
  X i := F ⋙ eval C (.down ℕ) i
  d i j := { app := fun n ↦ (F.obj n).d i j
             naturality := fun _ _ f ↦ (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).shape i j h
  d_comp_d' i j k hij hjk := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).d_comp_d i j k

/-- Evaluation of homology identifies with the original stage homologies. -/
def chainDiagramHomologyIso (F : J ⥤ ChainComplex C ℕ) (i : ℕ) :
    (chainDiagramComplex F).homology i ≅ F ⋙ homologyFunctor C (.down ℕ) i := by
  let K := chainDiagramComplex F
  refine NatIso.ofComponents (fun n ↦ ((K.sc i).mapHomologyIso
    ((evaluation J C).obj n)).symm) ?_
  intro n m f
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i)
    ((evaluation J C).map f)
  change homologyMap (F.map f) i =
    ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫ (K.homology i).map f ≫
      ((K.sc i).mapHomologyIso ((evaluation J C).obj m)).inv at h
  apply (cancel_epi ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map] using h.symm

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- Homology of the original termwise colimit complex is the colimit of stage homology. -/
def chainColimitHomologyIso (F : J ⥤ ChainComplex C ℕ) (i : ℕ) :
    ((coconeOfHasColimitEval F).pt).homology i ≅
      colimit (F ⋙ homologyFunctor C (.down ℕ) i) :=
  ((chainDiagramComplex F).sc i).mapHomologyIso (colim : (J ⥤ C) ⥤ C) ≪≫
    (colim : (J ⥤ C) ⥤ C).mapIso (chainDiagramHomologyIso F i)

/-- The homology comparison preserves each original standard inclusion into the colimit. -/
lemma chainColimitHomologyIso_ι (F : J ⥤ ChainComplex C ℕ) (i : ℕ) (n : J) :
    homologyMap ((coconeOfHasColimitEval F).ι.app n) i ≫
        (chainColimitHomologyIso F i).hom =
      colimit.ι (F ⋙ homologyFunctor C (.down ℕ) i) n := by
  let K := chainDiagramComplex F
  let τ : (evaluation J C).obj n ⟶ (colim : (J ⥤ C) ⥤ C) :=
    { app := fun D ↦ colimit.ι D n
      naturality := fun D E f ↦ (colimit.ι_map f n).symm }
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i) τ
  change homologyMap ((coconeOfHasColimitEval F).ι.app n) i =
    ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫ τ.app (K.homology i) ≫
      ((K.sc i).mapHomologyIso (colim : (J ⥤ C) ⥤ C)).inv at h
  rw [h]
  simp only [chainColimitHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  have hn := τ.naturality (chainDiagramHomologyIso F i).hom
  erw [hn.symm]
  change ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫
      ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).inv ≫
        τ.app (F ⋙ homologyFunctor C (.down ℕ) i) = _
  rw [Iso.hom_inv_id_assoc]

/-- Chain homology preserves colimits of the given shape whenever those colimits are exact. -/
lemma chainHomology_preservesExactColimits (i : ℕ) :
    PreservesColimitsOfShape J (homologyFunctor C (.down ℕ) i) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    apply IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ homologyFunctor C (.down ℕ) i))
    refine Cocone.ext (chainColimitHomologyIso F i).symm ?_
    intro n
    apply (cancel_mono (chainColimitHomologyIso F i).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (chainColimitHomologyIso_ι F i n).symm

end SerrePositivity
