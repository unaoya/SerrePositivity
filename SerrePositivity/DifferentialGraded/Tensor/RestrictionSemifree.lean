module
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Module.RestrictionGradedSplit
public import SerrePositivity.DifferentialGraded.Tensor.Semifree

/-! # 生成cellの制限からsemifree加群の制限の相対K-flat性を得る -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

/-- 制限されたsphere-free段階は、各生成cellの制限が相対K-flatなら相対K-flat。 -/
lemma sphereFreePresentation_restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSphereFreePresentation A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  let G := Discrete.functor fun t => freeSphere A E (S.object t) (S.degree t)
  have hc := moduleRelativeKFlat_colimit A D (G ⋙ moduleRestriction A D E F)
    (fun t => hfree (S.object t.as) (S.degree t.as))
  exact moduleRelativeKFlat_of_iso A D
    (((moduleRestriction A D E F).mapIso S.iso) ≪≫
      moduleRestrictionColimitIso A D E F G) hc

lemma ModuleSemifreeFiltration.restriction_relativeKFlat_stage
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) (n : ℕ) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (S.stage n))) := by
  induction n with
  | zero => exact sphereFreePresentation_restriction_relativeKFlat A D E F hfree S.initial
  | succ n ih =>
    exact moduleRelativeKFlat_of_gradedSplit A D ((S.split n).restrict A D E F) ih
      (sphereFreePresentation_restriction_relativeKFlat A D E F hfree (S.quotientPresentation n))

/-- 制限の余極限保存とfiltrationの網羅性から、全体の相対K-flat性を得る。 -/
lemma ModuleSemifreeFiltration.restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  let G := Functor.ofSequence S.transition
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have hc := moduleRelativeKFlat_colimit A D (G ⋙ moduleRestriction A D E F)
    (fun n => S.restriction_relativeKFlat_stage A D E F hfree n)
  let e : colimit G ≅ M := (colimit.isColimit G).coconePointUniqueUpToIso S.isColimit ≪≫ S.iso
  exact moduleRelativeKFlat_of_iso A D
    (((moduleRestriction A D E F).mapIso e.symm) ≪≫ moduleRestrictionColimitIso A D E F G) hc

lemma moduleSemifree_restriction_relativeKFlat
    (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (hM : moduleSemifree A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) := by
  obtain ⟨S⟩ := hM
  exact S.restriction_relativeKFlat A D E F hfree

end SerrePositivity.DifferentialGraded
