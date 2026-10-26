module
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Module.RestrictionGradedSplit
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective

/-!
概要：生成 sphere の実制限の射影性から semifree 加群の実制限の射影性を得る。
方針：全次数分裂の有限段と全射 Hom tower の実極限を使う。
規約：K-flat 性だけから射影性を推論しない。
使われ方：積 dg 圏上の固定 bimodule 解像度の各右制限。
-/
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

lemma ModuleSphereFreePresentation.restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSphereFreePresentation A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  have := S.smallIndex
  let e := PreservesCoproduct.iso (moduleRestriction A D E F)
    (fun t => freeSphere A E (S.object t) (S.degree t))
  exact moduleHomotopicallyProjective_of_iso A D
    (((moduleRestriction A D E F).mapIso S.iso) ≪≫ e).symm
    (moduleCoproduct_homotopicallyProjective A D _
      (fun t => hfree (S.object t) (S.degree t)))

lemma ModuleSemifreeFiltration.restriction_stage_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) (n : ℕ) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj (S.stage n)) := by
  induction n with
  | zero => exact S.initial.restriction_homotopicallyProjective A D E F hfree
  | succ n ih =>
    exact ((S.split n).restrict A D E F).homotopicallyProjective A D ih
      ((S.quotientPresentation n).restriction_homotopicallyProjective A D E F hfree)

lemma ModuleSemifreeFiltration.restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (S : ModuleSemifreeFiltration A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  apply moduleHomotopicallyProjective_of_iso A D ((moduleRestriction A D E F).mapIso S.iso)
  intro T hT
  apply complexTowerLimit_acyclic A
    (moduleHomSourceDiagram A D
      (Functor.ofSequence S.transition ⋙ moduleRestriction A D E F) T)
    (moduleColimitHomIsLimit A D
      (moduleRestrictionIsColimit A D E F S.cocone S.isColimit) T)
  · intro n
    exact S.restriction_stage_homotopicallyProjective A D E F hfree n T hT
  · intro n q
    change Function.Surjective
      ((eHomWhiskerRight (Complex A)
        ((moduleRestriction A D E F).map
          ((Functor.ofSequence S.transition).map (homOfLE (n.le_add_right 1)))) T).f q)
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact ((S.split n).restrict A D E F).homRestriction_surjective T q

lemma moduleSemifree_restriction_homotopicallyProjective
    (hfree : ∀ (x : E) (n : ℤ), moduleHomotopicallyProjective A D
      ((moduleRestriction A D E F).obj (freeSphere A E x n)))
    {M : ModuleCategory A E} (hM : moduleSemifree A E M) :
    moduleHomotopicallyProjective A D ((moduleRestriction A D E F).obj M) := by
  obtain ⟨S⟩ := hM
  exact S.restriction_homotopicallyProjective A D E F hfree

end SerrePositivity.DifferentialGraded
