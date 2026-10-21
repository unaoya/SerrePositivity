module

public import SerrePositivity.KST.LocalizingInvariants.CochainBoundaryFillingEpi
public import SerrePositivity.DifferentialGraded.Resolution.CycleCoverFunctor

/-!
概要：全射準同型を通る cycle と指定境界の、厳密な同時持ち上げを構成する。
方針：既存 mapping cone の境界持ち上げ計算を、実 cell の条件へ戻す。
規約：K-flat 性だけを入力にしない。使われ方：自由 dg 代数の cell 延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K L : Complex R} (p : K ⟶ L)
  (hs : ∀ n : ℤ, Function.Surjective (p.f n)) (hq : QuasiIso p)

include hs hq

lemma cochain_boundaryCell_filling_of_surjective_quasiIso (c : ComplexBoundaryCell R p) :
    c.HasFilling R :=
  complex_boundary_lifting_of_surjective_quasiIso R p hs hq c.degree
    c.cycle c.primitive c.boundary.symm

lemma cochain_cycle_lift_of_surjective_quasiIso (n : ℤ) (z : complexCycles R L n) :
    ∃ t : complexCycles R K n, p.f n t.val = z.val := by
  let c : ComplexBoundaryCell R p := {
    degree := n
    cycle := 0
    primitive := z.val
    boundary := by
      change L.d n (n + 1) z.val = p.f (n + 1) 0
      rw [map_zero]
      exact z.property }
  obtain ⟨t, ht, hp⟩ := cochain_boundaryCell_filling_of_surjective_quasiIso p hs hq c
  exact ⟨⟨t, ht⟩, hp⟩

lemma cochain_relative_primitive_lift {P : Complex R} (g : P ⟶ K) (q : P ⟶ L)
    (hg : g ≫ p = q) (c : ComplexBoundaryCell R q) :
    ∃ t : K.X c.degree,
      K.d c.degree (c.degree + 1) t = g.f (c.degree + 1) c.cycle.val ∧
        p.f c.degree t = c.primitive := by
  let z := complexMapCycle R g (c.degree + 1) c.cycle
  have hb : L.d c.degree (c.degree + 1) c.primitive = p.f (c.degree + 1) z.val := by
    have he := congrArg (fun f ↦ f.f (c.degree + 1) c.cycle.val) hg
    exact c.boundary.trans he.symm
  exact cochain_boundaryCell_filling_of_surjective_quasiIso p hs hq
    ⟨c.degree, z, c.primitive, hb⟩

end SerrePositivity.KST.LocalizingInvariants
