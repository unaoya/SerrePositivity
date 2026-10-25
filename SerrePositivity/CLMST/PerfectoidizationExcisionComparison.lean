module

public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationExcisionDiagram
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPullback

/-! # The exact canonical excision input for a perfectoidization comparison

All four maps are fixed by the original units. The only unprovided excision
input is the pullback property of this specified canonical square.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits BhattScholze
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The actual canonical excision square supplies both almost annihilators of
its top comparison, with exactly the pre-existing R-module structures. -/
theorem perfectoidization_comparison_almost_of_canonical_excision
    (hR : IsIntegralPerfectoid R p)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (a : R)
    (hPB : IsPullback
      (CommRingCat.ofHom (IsPerfectoidization.map hf hg q.toRingHom))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hf (Ideal.span {algebraMap R A a})))
      (CommRingCat.ofHom (perfectoidizationClosedSideProjection hg
        ((Ideal.span {algebraMap R A a}).map q.toRingHom)))
      (CommRingCat.ofHom (perfectoidizationClosedComparison hf hg q.toRingHom
        (Ideal.span {algebraMap R A a})))) :
    (∀ s ∈ perfectoidIdeal R p hR a,
      ∀ x : (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR a,
      ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.range, s • y = 0) := by
  let J : Ideal A := Ideal.span {algebraMap R A a}
  let L := QuotientPerfectoidization C (J.map f.toRingHom) p hf.1
  let T := QuotientPerfectoidization D ((J.map q.toRingHom).map g.toRingHom) p hg.1
  let l := perfectoidizationClosedSideProjection hf J
  let r := perfectoidizationClosedSideProjection hg (J.map q.toRingHom)
  let b := perfectoidizationClosedComparison hf hg q.toRingHom J
  let m := IsPerfectoidization.mapAlgHom hf hg q
  let : Algebra R L := (l.comp (algebraMap R C)).toAlgebra
  let : Algebra R T := (r.comp (algebraMap R D)).toAlgebra
  let l' : C →ₐ[R] L := { l with commutes' := fun _ => rfl }
  let r' : D →ₐ[R] T := { r with commutes' := fun _ => rfl }
  let b' : L →ₐ[R] T :=
    { b with
      commutes' := by
        intro s
        have h := RingHom.congr_fun
          (perfectoidizationClosedComparison_square hf hg q.toRingHom J) (algebraMap R C s)
        change b (l (algebraMap R C s)) = r (m (algebraMap R C s)) at h
        rw [m.commutes] at h
        exact h }
  have hL : IsIntegralPerfectoid L p :=
    (isPerfectoidization_toQuotientPerfectoidization C (J.map f.toRingHom) p hf.1).1
  have ha : algebraMap R L a = 0 := by
    change l (algebraMap R C a) = 0
    rw [← f.commutes]
    exact perfectoidizationClosedSideProjection_eq_zero_of_mem hf J (algebraMap R A a)
      (Ideal.subset_span (Set.mem_singleton _))
  exact perfectoidIdeal_ker_coker_annihilated_of_isPullback hR m l' r' b' hPB hL a ha

end SerrePositivity.CLMST
