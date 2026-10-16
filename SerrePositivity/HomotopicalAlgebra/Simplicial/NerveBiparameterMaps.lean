module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameter
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentReindex

/-! # Actual reindexing and parameter/value maps of two-endpoint coherent families -/

@[expose] public section
universe v u w vE uE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type u} [Category.{v} D]
  (L K F : D ⥤ SSet.{w}) (i : L ⟶ K)

def restriction : NerveBiparameter.values K F ⟶ NerveBiparameter.values L F :=
  Functor.whiskerLeft (NerveBiparameter.endpoints D)
    (Functor.whiskerRight (NatTrans.prod (NatTrans.op i) (𝟙 F))
      (Functor.uncurry.obj MonoidalClosed.internalHom))

lemma restriction_app (s : Index D) : (restriction L K F i).app s =
    (pre (i.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) := by
  change (pre (i.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) ≫
    (ihom (L.obj (NerveSimplexStart.start s))).map (𝟙 (F.obj (endpoint s))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

lemma restriction_comp (M : D ⥤ SSet.{w}) (k : K ⟶ M) :
    restriction K M F k ≫ restriction L K F i = restriction L M F (i ≫ k) := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, restriction_app]
  exact (congr_app (pre_map (i.app (NerveSimplexStart.start s))
    (k.app (NerveSimplexStart.start s))) (F.obj (endpoint s))).symm

def restrict (a : NerveBiparameter.System K F) : NerveBiparameter.System L F :=
  a ≫ restriction L K F i

lemma restrict_component (a : NerveBiparameter.System K F) (s : Index D) :
    (restrict L K F i a).app s = a.app s ≫
      (pre (i.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) := by
  change a.app s ≫ (restriction L K F i).app s = _
  rw [restriction_app]

variable (G : D ⥤ SSet.{w}) (p : F ⟶ G)

def targetMap : NerveBiparameter.values K F ⟶ NerveBiparameter.values K G :=
  Functor.whiskerLeft (NerveBiparameter.endpoints D)
    (Functor.whiskerRight (NatTrans.prod (𝟙 K.op) p)
      (Functor.uncurry.obj MonoidalClosed.internalHom))

lemma targetMap_app (s : Index D) : (targetMap K F G p).app s =
    (ihom (K.obj (NerveSimplexStart.start s))).map (p.app (endpoint s)) := by
  change (pre (𝟙 (K.obj (NerveSimplexStart.start s)))).app (F.obj (endpoint s)) ≫ _ = _
  rw [pre_id]
  exact Category.id_comp _

def mapTarget (a : NerveBiparameter.System K F) : NerveBiparameter.System K G :=
  a ≫ targetMap K F G p

lemma mapTarget_component (a : NerveBiparameter.System K F) (s : Index D) :
    (mapTarget K F G p a).app s = a.app s ≫
      (ihom (K.obj (NerveSimplexStart.start s))).map (p.app (endpoint s)) := by
  change a.app s ≫ (targetMap K F G p).app s = _
  rw [targetMap_app]

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma start_map {s t : Index E} (f : s ⟶ t) :
    NerveSimplexStart.startMap ((NerveCoherentReindex.index H).map f) =
      H.map (NerveSimplexStart.startMap f) := by
  dsimp only [NerveSimplexStart.startMap, NerveSimplexStart.initialSegment]
  rw [H.map_comp, eqToHom_map]
  rfl

/-- Reindex both endpoints without imposing equal object or Hom universes. -/
def reindex (a : NerveBiparameter.System K F) : NerveBiparameter.System (H ⋙ K) (H ⋙ F) where
  app s := a.app ((NerveCoherentReindex.index H).obj s)
  naturality {s t} f := by
    have h := NerveBiparameter.compatibility K F a ((NerveCoherentReindex.index H).map f)
    change SSet.stdSimplex.map (operator f) ≫ a.app ((NerveCoherentReindex.index H).obj t) =
      a.app ((NerveCoherentReindex.index H).obj s) ≫
        (pre (K.map (H.map (NerveSimplexStart.startMap f)))).app (F.obj (H.obj (endpoint s))) ≫
        (ihom (K.obj (H.obj (NerveSimplexStart.start t)))).map (F.map (H.map (endpointMap f)))
    rw [← start_map H f, ← NerveCoherentReindex.endpoint_map H f]
    exact h

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
