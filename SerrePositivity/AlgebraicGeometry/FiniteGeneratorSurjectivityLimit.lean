module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
概要：後段に一様な有限個の代数生成元の原像から、有限段の環写像の全射性を得る。
方針：余極限から原像を取り、像との一致を後段へ移し、有限族の射を一つにそろえる。
規約：Stacks 07RH の有限生成元の議論。tensor の生成元の供給は別に扱う。
使われ方：C04 の affine な閉埋め込み性の代数的な降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v

/-- 余極限で全射で、一様な有限個の生成元があれば、ある後段の環写像は全射。 -/
theorem exists_surjective_stage_of_uniform_generators
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D E : J ⥤ CommRingCat.{u}) (τ : D ⟶ E)
    (cD : Cocone D) (cE : Cocone E) (hD : IsColimit cD) (hE : IsColimit cE)
    (φ : cD.pt ⟶ cE.pt) (hφ : Function.Surjective φ)
    (hcomm : ∀ j, cD.ι.app j ≫ φ = τ.app j ≫ cE.ι.app j)
    {ι : Type v} [Finite ι] (i : J) (s : ι → E.obj i)
    (hgen : ∀ (j : J) (f : i ⟶ j),
      Subring.closure (Set.range (τ.app j) ∪ Set.range (fun a ↦ E.map f (s a))) = ⊤) :
    ∃ (j : J) (_ : i ⟶ j), Function.Surjective (τ.app j) := by
  classical
  have hD' := isColimitOfPreserves (forget CommRingCat.{u}) hD
  have hE' := isColimitOfPreserves (forget CommRingCat.{u}) hE
  choose x hx using fun a ↦ hφ (cE.ι.app i (s a))
  choose k y hy using fun a ↦ Types.jointly_surjective_of_isColimit hD' (x a)
  have heq (a : ι) : cE.ι.app (k a) (τ.app (k a) (y a)) = cE.ι.app i (s a) := by
    calc
      _ = φ (cD.ι.app (k a) (y a)) :=
        (congrArg (fun z : D.obj (k a) ⟶ cE.pt ↦ z (y a)) (hcomm (k a))).symm
      _ = φ (x a) := congrArg φ (hy a)
      _ = _ := hx a
  choose l f g hfg using fun a ↦ (Types.FilteredColimit.isColimit_eq_iff _ hE').mp (heq a)
  obtain ⟨j, hij, r, hr⟩ := IsFiltered.wideSpan g
  refine ⟨j, hij, ?_⟩
  apply (RingHom.range_eq_top (f := (τ.app j).hom)).mp
  apply top_unique
  rw [← hgen j hij]
  apply Subring.closure_le.mpr
  rintro z (hz | hz)
  · exact hz
  · obtain ⟨a, rfl⟩ := hz
    refine ⟨D.map (r a) (D.map (f a) (y a)), ?_⟩
    calc
      _ = E.map (r a) (τ.app (l a) (D.map (f a) (y a))) :=
        congrArg (fun z : D.obj (l a) ⟶ E.obj j ↦ z (D.map (f a) (y a))) (τ.naturality (r a))
      _ = E.map (r a) (E.map (f a) (τ.app (k a) (y a))) :=
        congrArg (E.map (r a))
          (congrArg (fun z : D.obj (k a) ⟶ E.obj (l a) ↦ z (y a)) (τ.naturality (f a)))
      _ = E.map (r a) (E.map (g a) (s a)) := congrArg (E.map (r a)) (hfg a)
      _ = E.map hij (s a) := by
        simpa only [Functor.map_comp, CommRingCat.comp_apply] using
          congrArg (fun z : i ⟶ j ↦ E.map z (s a)) (hr a)

end SerrePositivity.AlgebraicGeometry
