module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # filtered余極限のcycleの有限段表示

任意可換環上の非有界複体について、cycleの微分が零となる段階まで添字を進める。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]
variable (F : ℕ ⥤ Complex A) (s : Cocone F)

/-- 可算filtered余極限のcycleは、ある有限段のcycleの像である。 -/
lemma complexSequentialColimit_cycle_rep (hs : IsColimit s) (n : ℤ) (z : complexCycles A s.pt n) :
    ∃ (k : ℕ) (t : complexCycles A (F.obj k) n), (s.ι.app k).f n t.val = z.val := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let Fn := F ⋙ ev n
  let sn := (ev n).mapCocone s
  have hn : IsColimit sn := isColimitOfPreserves (ev n) hs
  obtain ⟨j, t, ht⟩ := Concrete.isColimit_exists_rep Fn hn z.val
  change (s.ι.app j).f n t = z.val at ht
  let Fn' := F ⋙ ev (n + 1)
  have hn' : IsColimit ((ev (n + 1)).mapCocone s) :=
    isColimitOfPreserves (ev (n + 1)) hs
  have hz : (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) = 0 := by
    have h := congrArg (fun f => f t) ((s.ι.app j).comm n (n + 1))
    change (s.pt.d n (n + 1)) ((s.ι.app j).f n t) =
      (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) at h
    exact h.symm.trans (ht ▸ z.property)
  obtain ⟨k, f, g, hk⟩ := Concrete.isColimit_exists_of_rep_eq Fn' hn'
    ((F.obj j).d n (n + 1) t) (0 : (F.obj j).X (n + 1)) (by
      change (s.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) t) = (s.ι.app j).f (n + 1) 0
      simpa only [map_zero] using hz)
  change (F.map f).f (n + 1) ((F.obj j).d n (n + 1) t) = (F.map g).f (n + 1) 0 at hk
  rw [map_zero] at hk
  have hc : (F.obj k).d n (n + 1) ((F.map f).f n t) = 0 := by
    have h := congrArg (fun a => a t) ((F.map f).comm n (n + 1))
    exact h.trans hk
  refine ⟨k, ⟨(F.map f).f n t, hc⟩, ?_⟩
  have h := congrArg (fun a => a.f n t) (s.ι.naturality f)
  change (s.ι.app k).f n ((F.map f).f n t) = (s.ι.app j).f n t at h
  exact h.trans ht

end SerrePositivity.DifferentialGraded
