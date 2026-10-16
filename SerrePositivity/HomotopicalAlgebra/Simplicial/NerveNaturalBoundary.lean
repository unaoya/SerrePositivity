module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

/-! # Whole coherent moving boundaries induced by actual natural transformations -/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveNaturalBoundary
variable {D : Type uD} [Category.{vD} D]

abbrev whole (s : Index D) := (chain s).map (homOfLE (Fin.zero_le (Fin.last (dimension s))))

lemma span {n m : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (h : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c) :
    NerveSimplexStart.initialSegment c d θ h ≫
      c.map (homOfLE (Fin.zero_le (Fin.last n))) ≫ tail c d θ h =
        d.map (homOfLE (Fin.zero_le (Fin.last m))) := by
  subst c
  simp only [NerveSimplexStart.initialSegment, tail, eqToHom_refl, Category.comp_id,
    Category.id_comp, Functor.comp_map]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

lemma whole_naturality {s t : Index D} (f : s ⟶ t) :
    NerveSimplexStart.startMap f ≫ whole s ≫ endpointMap f = whole t :=
  span (chain s) (chain t) (operator f) (chain_eq f)

variable (K F : D ⥤ SSet.{w}) (b : K ⟶ F)

abbrev family (s : Index D) : K.obj (NerveSimplexStart.start s) ⟶ F.obj (endpoint s) :=
  b.app (NerveSimplexStart.start s) ≫ F.map (whole s)

lemma family_naturality {s t : Index D} (f : s ⟶ t) :
    K.map (NerveSimplexStart.startMap f) ≫ family K F b s ≫ F.map (endpointMap f) =
      family K F b t := by
  dsimp only [family]
  rw [← Category.assoc, ← Category.assoc, b.naturality]
  simp only [Category.assoc]
  rw [← F.map_comp, ← F.map_comp, whole_naturality]

/-- A strict natural boundary determines its whole coherent system without new choices. -/
def ofNatTrans : NerveBiparameter.System K F where
  app s := SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (family K F b s)
  naturality {s t} f := by
    have hn : (RelativeChoiceSpace.name (family K F b s) ≫
        (pre (K.map (NerveSimplexStart.startMap f))).app (F.obj (endpoint s))) ≫
      (ihom (K.obj (NerveSimplexStart.start t))).map (F.map (endpointMap f)) =
        RelativeChoiceSpace.name (family K F b t) := by
      rw [show RelativeChoiceSpace.name (family K F b s) ≫
          (pre (K.map (NerveSimplexStart.startMap f))).app (F.obj (endpoint s)) =
        RelativeChoiceSpace.name (K.map (NerveSimplexStart.startMap f) ≫ family K F b s) from
          RelativeChoiceSpace.name_precomp _ _]
      rw [RelativeChoiceSpace.name_postcomp, Category.assoc, family_naturality]
    change SSet.stdSimplex.map (operator f) ≫
        (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (family K F b t)) =
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name (family K F b s)) ≫
        (pre (K.map (NerveSimplexStart.startMap f))).app (F.obj (endpoint s)) ≫
          (ihom (K.obj (NerveSimplexStart.start t))).map (F.map (endpointMap f))
    rw [← Category.assoc, show SSet.stdSimplex.map (operator f) ≫
        SSet.stdSimplex.isTerminalObj₀.from _ = SSet.stdSimplex.isTerminalObj₀.from _ from
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
    simpa only [Category.assoc] using
      (congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ e) hn).symm

lemma whole_zero (s : Index D) (h : dimension s = 0) :
    whole s = eqToHom (NerveMovingParameter.start_eq_endpoint_zero s h) := by
  have he : (0 : Fin (dimension s + 1)) = Fin.last (dimension s) := Fin.ext h.symm
  have hh : homOfLE (Fin.zero_le (Fin.last (dimension s))) = eqToHom he := Subsingleton.elim _ _
  unfold whole
  rw [hh, eqToHom_map]

lemma ofNatTrans_zero (s : Index D) (h : dimension s = 0) : (ofNatTrans K F b).app s =
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
      (b.app (NerveSimplexStart.start s) ≫
        eqToHom (congrArg F.obj (NerveMovingParameter.start_eq_endpoint_zero s h))) := by
  change SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (b.app _ ≫ F.map (whole s)) = _
  rw [whole_zero s h, eqToHom_map]

end SerrePositivity.SimplicialModel.NerveNaturalBoundary
