module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutCotensor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-! # Gluing whole coherent moving parameter systems along a diagram pushout -/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NervePushoutBoundary
variable {D : Type uD} [Category.{vD} D] (A B C F : D ⥤ SSet.{w}) (u : A ⟶ B) (v : A ⟶ C)

abbrev parameter : D ⥤ SSet.{w} := pushout u v
abbrev left : B ⟶ parameter A B C u v := pushout.inl u v
abbrev right : C ⟶ parameter A B C u v := pushout.inr u v

lemma square (d : D) : IsPushout (u.app d) (v.app d)
    ((left A B C u v).app d) ((right A B C u v).app d) :=
  ((evaluation D SSet.{w}).obj d).map_isPushout (IsPushout.of_hasPushout u v)

variable (b : NerveBiparameter.System B F) (c : NerveBiparameter.System C F)
  (h : b ≫ NerveBiparameterMaps.restriction A B F u =
    c ≫ NerveBiparameterMaps.restriction A C F v)

include h in
lemma component_compatible (s : Index D) : b.app s ≫ (pre (u.app
    (NerveSimplexStart.start s))).app (F.obj (endpoint s)) = c.app s ≫
    (pre (v.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) := by
  have he := congr_app h s
  simpa only [NatTrans.comp_app, NerveBiparameterMaps.restriction_app] using he

/-- Retain both entire systems on the two pieces of the actual parameter pushout. -/
def glue : NerveBiparameter.System (parameter A B C u v) F where
  app s := PushoutCotensor.glue (square A B C u v (NerveSimplexStart.start s))
    (b.app s) (c.app s) (component_compatible A B C F u v b c h s)
  naturality {s t} f := by
    apply PushoutCotensor.hom_ext (square A B C u v (NerveSimplexStart.start t))
    · simp only [Category.assoc, PushoutCotensor.glue_left]
      have hn := (NerveBiparameterMaps.restriction B (parameter A B C u v) F
        (left A B C u v)).naturality f
      rw [NerveBiparameterMaps.restriction_app, NerveBiparameterMaps.restriction_app] at hn
      have hg := PushoutCotensor.glue_left
        (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
        (component_compatible A B C F u v b c h s)
      exact (b.naturality f).trans
        ((congrArg (fun k => k ≫ (NerveBiparameter.values B F).map f) hg.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => PushoutCotensor.glue
              (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
              (component_compatible A B C F u v b c h s) ≫ k) hn.symm)))
    · simp only [Category.assoc, PushoutCotensor.glue_right]
      have hn := (NerveBiparameterMaps.restriction C (parameter A B C u v) F
        (right A B C u v)).naturality f
      rw [NerveBiparameterMaps.restriction_app, NerveBiparameterMaps.restriction_app] at hn
      have hg := PushoutCotensor.glue_right
        (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
        (component_compatible A B C F u v b c h s)
      exact (c.naturality f).trans
        ((congrArg (fun k => k ≫ (NerveBiparameter.values C F).map f) hg.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun k => PushoutCotensor.glue
              (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
              (component_compatible A B C F u v b c h s) ≫ k) hn.symm)))

lemma glue_left : glue A B C F u v b c h ≫ NerveBiparameterMaps.restriction
    B (parameter A B C u v) F (left A B C u v) = b := by
  apply NatTrans.ext
  funext s
  change (glue A B C F u v b c h).app s ≫ _ = _
  rw [NerveBiparameterMaps.restriction_app]
  exact PushoutCotensor.glue_left
    (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
    (component_compatible A B C F u v b c h s)

lemma glue_right : glue A B C F u v b c h ≫ NerveBiparameterMaps.restriction
    C (parameter A B C u v) F (right A B C u v) = c := by
  apply NatTrans.ext
  funext s
  change (glue A B C F u v b c h).app s ≫ _ = _
  rw [NerveBiparameterMaps.restriction_app]
  exact PushoutCotensor.glue_right
    (square A B C u v (NerveSimplexStart.start s)) (b.app s) (c.app s)
    (component_compatible A B C F u v b c h s)

end SerrePositivity.SimplicialModel.NervePushoutBoundary
