module
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import SerrePositivity.DifferentialGraded.Module.Colimits

/-! # 評価による主dg加群圏の同型・余極限の反映 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各評価が同型である主加群射は同型。逆射も全dg自然。 -/
lemma moduleIsIso_of_evaluations {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : ∀ x : D, IsIso ((moduleEvaluation A D x).map f)) : IsIso f := by
  let (x : D) : IsIso ((moduleEvaluation A D x).map f) := hf x
  let e : M ≅ N := moduleIsoMk A D
    (fun x : Dᵒᵖ => asIso ((moduleEvaluation A D x.unop).map f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f))
  have he : e.hom = f := by
    apply moduleMorphism_ext
    intro x
    exact moduleIsoMk_hom_eval A D _ _ x
  rw [← he]
  infer_instance

/-- 各評価の余極限が存在する図式について、全評価の余極限性を反映する。 -/
def moduleIsColimitOfEvaluations {J : Type w} [Category.{w'} J]
    {F : J ⥤ ModuleCategory A D}
    [∀ x : Dᵒᵖ, HasColimit (F ⋙ moduleEvaluation A D x.unop)] (c : Cocone F)
    (hc : ∀ x : D, IsColimit ((moduleEvaluation A D x).mapCocone c)) : IsColimit c := by
  let : IsIso (moduleColimitDesc A D F c) :=
    moduleIsIso_of_evaluations A D (moduleColimitDesc A D F c) (by
      intro x
      rw [moduleColimitDesc_eval]
      exact inferInstanceAs (IsIso
        ((colimit.isColimit (F ⋙ moduleEvaluation A D x)).coconePointUniqueUpToIso (hc x)).hom))
  let e : moduleColimitCocone A D F ≅ c :=
    Cocone.ext (asIso (moduleColimitDesc A D F c))
      (fun j => (moduleColimitCoconeIsColimit A D F).fac c j)
  exact IsColimit.ofIsoColimit (moduleColimitCoconeIsColimit A D F) e

end SerrePositivity.DifferentialGraded
