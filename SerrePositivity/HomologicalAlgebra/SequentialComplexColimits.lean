module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Transposing cochain diagrams and exact sequential colimits -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u w t
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {T : Type t} [Category.{w} T]

/-- Transpose a functor to cochain complexes into a cochain complex of functors. -/
def functorCochainComplex (F : T ⥤ CochainComplex C ℕ) : CochainComplex (T ⥤ C) ℕ where
  X i := F ⋙ eval C (.up ℕ) i
  d i j :=
    { app := fun n => (F.obj n).d i j
      naturality := fun _ _ f => (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).shape i j h
  d_comp_d' i j k hij hjk := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).d_comp_d i j k

/-- Transposition also acts functorially on all morphisms of complex-valued functors. -/
def functorCochainComplexFunctor (T : Type t) [Category.{w} T] (C : Type u)
    [Category.{v} C] [Abelian C] :
    (T ⥤ CochainComplex C ℕ) ⥤ CochainComplex (T ⥤ C) ℕ where
  obj F := functorCochainComplex F
  map α :=
    { f := fun i => Functor.whiskerRight α (eval C (.up ℕ) i)
      comm' := by
        intro i j hij
        apply NatTrans.ext
        funext n
        exact (α.app n).comm i j }
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply NatTrans.ext
    funext n
    rfl
  map_comp α β := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply NatTrans.ext
    funext n
    rfl

/-- Homology of the transposed complex is naturally the functor of stage homologies. -/
def functorCochainHomologyIso (F : T ⥤ CochainComplex C ℕ) (i : ℕ) :
    (functorCochainComplex F).homology i ≅ F ⋙ homologyFunctor C (.up ℕ) i := by
  let K := functorCochainComplex F
  refine NatIso.ofComponents (fun n => ((K.sc i).mapHomologyIso
    ((evaluation T C).obj n)).symm) ?_
  intro n m f
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i)
    ((evaluation T C).map f)
  change homologyMap (F.map f) i =
    ((K.sc i).mapHomologyIso ((evaluation T C).obj n)).hom ≫ (K.homology i).map f ≫
      ((K.sc i).mapHomologyIso ((evaluation T C).obj m)).inv at h
  apply (cancel_epi ((K.sc i).mapHomologyIso ((evaluation T C).obj n)).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map] using h.symm

/-- The stage-homology comparison is natural in the entire complex-valued functor. -/
def functorCochainHomologyNatIso (T : Type t) [Category.{w} T] (C : Type u)
    [Category.{v} C] [Abelian C] (i : ℕ) :
    functorCochainComplexFunctor T C ⋙ homologyFunctor (T ⥤ C) (.up ℕ) i ≅
      (Functor.whiskeringRight T (CochainComplex C ℕ) C).obj (homologyFunctor C (.up ℕ) i) := by
  refine NatIso.ofComponents (fun F => functorCochainHomologyIso F i) ?_
  intro F G α
  apply NatTrans.ext
  funext n
  exact CategoryTheory.ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (T ⥤ C) (.up ℕ) i).map
      ((functorCochainComplexFunctor T C).map α)) ((evaluation T C).obj n)

/-- Reading a complex of functors as a functor of complexes preserves its actual homology. -/
def asFunctorCochainHomologyIso (K : CochainComplex (T ⥤ C) ℕ) (i : ℕ) :
    K.asFunctor ⋙ homologyFunctor C (.up ℕ) i ≅ K.homology i :=
  (functorCochainHomologyIso K.asFunctor i).symm

/-- Transpose a sequential cochain diagram to a complex of sequential diagrams. -/
abbrev sequentialCochainDiagramComplex (F : ℕ ⥤ CochainComplex C ℕ) :
    CochainComplex (ℕ ⥤ C) ℕ := functorCochainComplex F

/-- The homology comparison for a sequential cochain diagram. -/
abbrev sequentialCochainDiagramHomologyIso (F : ℕ ⥤ CochainComplex C ℕ) (i : ℕ) :
    (sequentialCochainDiagramComplex F).homology i ≅ F ⋙ homologyFunctor C (.up ℕ) i :=
  functorCochainHomologyIso F i

variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]

/-- The termwise sequential colimit complex, formed by the exact colimit functor. -/
def sequentialCochainColimit (F : ℕ ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  ((colim : (ℕ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℕ)).obj (sequentialCochainDiagramComplex F)

/-- Exact colimits give the actual homology-colimit comparison. -/
def sequentialCochainColimitHomologyIso (F : ℕ ⥤ CochainComplex C ℕ) (i : ℕ) :
    (sequentialCochainColimit F).homology i ≅ colimit (F ⋙ homologyFunctor C (.up ℕ) i) :=
  ((sequentialCochainDiagramComplex F).sc i).mapHomologyIso (colim : (ℕ ⥤ C) ⥤ C) ≪≫
    (colim : (ℕ ⥤ C) ⥤ C).mapIso (sequentialCochainDiagramHomologyIso F i)

/-- This termwise colimit complex is the actual categorical colimit of the diagram. -/
def sequentialCochainColimitIso (F : ℕ ⥤ CochainComplex C ℕ) :
    sequentialCochainColimit F ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F) (colimit.isColimit F)

/-- Homology of the actual categorical sequential colimit is the colimit of homology. -/
def sequentialCochainHomologyColimitIso (F : ℕ ⥤ CochainComplex C ℕ) (i : ℕ) :
    (colimit F).homology i ≅ colimit (F ⋙ homologyFunctor C (.up ℕ) i) :=
  (homologyFunctor C (.up ℕ) i).mapIso (sequentialCochainColimitIso F).symm ≪≫
    sequentialCochainColimitHomologyIso F i

end SerrePositivity
