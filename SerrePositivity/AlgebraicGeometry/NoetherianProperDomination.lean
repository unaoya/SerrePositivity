module

public import SerrePositivity.AlgebraicGeometry.NoetherianComponentFamily
public import SerrePositivity.AlgebraicGeometry.IrreducibleNoetherianProperDomination
public import SerrePositivity.AlgebraicGeometry.FiniteProperDominationUnion

/-!
概要：一般の Noether 対象を、固有な周辺への開包含を持つ実際の固有全射で覆う。
方針：既存の既約成分への支配を有限直和でまとめる。
規約：元の対象の被約性や固有性を要求しない。
使われ方：C06 の Chow の形。一般の固有性の有限段への降下の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 一般の Noether 対象は、固有な周辺への開包含を持つ固有全射で覆われる。 -/
theorem exists_noetherian_proper_domination {X S : Scheme.{u}}
    [IsNoetherian X] [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] :
    ∃ (T P : Scheme.{u}) (h : T ⟶ X) (t : T ⟶ P) (q : P ⟶ S),
      IsProper h ∧ Surjective h ∧ IsOpenImmersion t ∧ IsProper q ∧ t ≫ q = h ≫ f := by
  classical
  let C := noetherianComponentIndex X
  letI : Finite C := noetherianComponentIndex_finite X
  letI : Fintype C := Fintype.ofFinite C
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  have hc (z : C) := isClosedImmersion_noetherianComponentInclusion X z
  letI (z : C) : IsClosedImmersion (noetherianComponentInclusion X z) := hc z
  letI (z : C) : IsNoetherian (noetherianComponentScheme X z) :=
    isNoetherian_noetherianComponentScheme X z
  letI (z : C) : IrreducibleSpace (noetherianComponentScheme X z) :=
    irreducibleSpace_noetherianComponentScheme X z
  have H (z : C) := exists_irreducible_noetherian_proper_domination
    (noetherianComponentInclusion X z ≫ f)
  choose T P h t q hh hs ht hq hcomm using H
  let hFin (i : Fin (Fintype.card C)) :=
    h (e.symm i) ≫ noetherianComponentInclusion X (e.symm i)
  have hhFin (i : Fin (Fintype.card C)) : IsProper (hFin i) := by
    letI : IsProper (h (e.symm i)) := hh (e.symm i)
    dsimp [hFin]
    infer_instance
  have hcommFin (i : Fin (Fintype.card C)) :
      t (e.symm i) ≫ q (e.symm i) = hFin i ≫ f := by
    simpa only [hFin, Category.assoc] using hcomm (e.symm i)
  obtain ⟨T', P', h', t', q', l, hh', ht', hq', hcomm', hl⟩ :=
    exists_finite_proper_domination_union f (Fintype.card C)
      (fun i ↦ T (e.symm i)) (fun i ↦ P (e.symm i)) hFin
      (fun i ↦ t (e.symm i)) (fun i ↦ q (e.symm i)) hhFin
      (fun i ↦ ht (e.symm i)) (fun i ↦ hq (e.symm i)) hcommFin
  have hs' : Surjective h' := by
    constructor
    intro x
    obtain ⟨z, y, hy⟩ := noetherianComponentInclusion_jointly_surjective X x
    obtain ⟨i, rfl⟩ := e.symm.surjective z
    obtain ⟨v, hv⟩ := (hs (e.symm i)).surj y
    have hvx : hFin i v = x := by
      change noetherianComponentInclusion X (e.symm i) (h (e.symm i) v) = x
      rw [hv, hy]
    refine ⟨l i v, ?_⟩
    have hpoint := congrArg (fun k ↦ k v) (hl i)
    simpa only [Scheme.Hom.comp_apply] using hpoint.trans hvx
  exact ⟨T', P', h', t', q', hh', hs', ht', hq', hcomm'⟩

end SerrePositivity.AlgebraicGeometry
