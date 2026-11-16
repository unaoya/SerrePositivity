module

public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Cover

/-! # perfectoid 化の比較の標準 excision の入力

## 概要

四つの写像をすべて元の普遍単位で固定した標準の四角について、それが引き戻しなら perfectoid 化の比較写像が almost 同型になることを示す（`perfectoidization_comparison_almost_of_canonical_excision`）。
BS 著者版 Corollary 8.12 の excision を、有限比較で使う標準四角形に適用する。

## 規約

仮定として残す excision の入力は、この指定した標準の四角の引き戻しの性質だけ。旧 `CLMST/PerfectoidizationExcisionComparison`。

## 使われ方

CLMST の KL 比較（標準 excision の Tor 入力）。
-/

@[expose] public noncomputable section

universe u

section PerfectoidizationExcisionComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.BhattScholze
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
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
      ∀ x : (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR a,
      ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.range, s • y = 0) := by
  let J : Ideal A := Ideal.span {algebraMap R A a}
  let L := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization C (J.map f.toRingHom) p hf.1
  let T := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization D ((J.map q.toRingHom).map g.toRingHom) p hg.1
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
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization C (J.map f.toRingHom) p hf.1).1
  have ha : algebraMap R L a = 0 := by
    change l (algebraMap R C a) = 0
    rw [← f.commutes]
    exact perfectoidizationClosedSideProjection_eq_zero_of_mem hf J (algebraMap R A a)
      (Ideal.subset_span (Set.mem_singleton _))
  exact _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_ker_coker_annihilated_of_isPullback hR m l' r' b' hPB hL a ha

end SerrePositivity.BhattScholze

end PerfectoidizationExcisionComparisonPart
