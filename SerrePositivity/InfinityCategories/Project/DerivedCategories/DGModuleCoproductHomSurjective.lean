module
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
/-!
概要：余積を始域とする Hom の次数別全射性を実普遍性で構成する。
方針：実全次数 Hom と評価・余積の既存の普遍性を使う。
規約：全 dg 自然性と元の後合成射を保つ。使われ方：strict cell lift。
-/
@[expose] public section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex MonoidalCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleCoproductHom_postcompose_surjective
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {J : Type w} [Small.{u} J] (M : J → ModuleCategory R D)
    {T N : ModuleCategory R D} (q : T ⟶ N)
    (hq : ∀ (j : J) (p : ℤ),
      Function.Surjective ((eHomWhiskerLeft (Complex R) (M j) q).f p)) (p : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex R) (∐ M) q).f p) := by
  intro z
  have hj : ∀ j : J, ∃ a,
      (eHomWhiskerLeft (Complex R) (M j) q).f p a =
        (eHomWhiskerRight (Complex R) (Sigma.ι M j) N).f p z := by
    intro j
    exact hq j p _
  choose a ha using hj
  let hc : IsLimit (Fan.mk
      ((moduleHom R D (ForgetEnrichment.to (Complex R) (∐ M))
        (ForgetEnrichment.to (Complex R) T)).X p)
      (fun j => (eHomWhiskerRight (Complex R) (Sigma.ι M j) T).f p)) :=
    isLimitFanMkObjOfIsLimit (HomologicalComplex.eval (ModuleCat R) (.up ℤ) p)
      (moduleCoproductHomFamily R D M T)
      (fun j => eHomWhiskerRight (Complex R) (Sigma.ι M j) T)
      (moduleCoproductHomIsLimit R D M T)
  let g := Fan.IsLimit.lift hc (fun j => moduleElementMap R _ (a j))
  let x := g (1 : R)
  have hx : ∀ j : J, (eHomWhiskerRight (Complex R) (Sigma.ι M j) T).f p x = a j := by
    intro j
    have he := congrArg (fun t => t (1 : R))
      (Fan.IsLimit.fac hc (fun j => moduleElementMap R _ (a j)) j)
    change (eHomWhiskerRight (Complex R) (Sigma.ι M j) T).f p x = (1 : R) • a j at he
    exact he.trans (one_smul R _)
  refine ⟨x, ?_⟩
  apply complexLimitDegree_element_ext R (moduleCoproductHomIsLimit R D M N) p
  intro j
  have he := congrArg (fun c => c.f p x)
    (eHom_whisker_exchange (Complex R) (Sigma.ι M j.as) q)
  change (eHomWhiskerRight (Complex R) (Sigma.ι M j.as) N).f p
      ((eHomWhiskerLeft (Complex R) (∐ M) q).f p x) =
    (eHomWhiskerLeft (Complex R) (M j.as) q).f p
      ((eHomWhiskerRight (Complex R) (Sigma.ι M j.as) T).f p x) at he
  exact he.trans ((congrArg ((eHomWhiskerLeft (Complex R) (M j.as) q).f p) (hx j.as)).trans
    (ha j.as))
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
