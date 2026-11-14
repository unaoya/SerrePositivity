module

public import SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationExact

/-!
概要：指定した加法同型と可換な射で短完全列を移す。
方針：単射性、核と像、全射性をそれぞれ同型で反映する。
規約：新しい射が古い射と可換であることを明示的に要求する。
使われ方：切断環の完全列を実際の Čech H⁰ の四角形へ移す。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
universe u v w v' w'
variable {A : Type u} {B : Type v} {C : Type w} {B' : Type v'} {C' : Type w'}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup B'] [AddCommGroup C']

/-- 指定した加法同型と可換な射への短完全列の移送。 -/
theorem cechAdditiveShortExact_transport (f : A →+ B) (g : B →+ C)
    (e : B' ≃+ B) (d : C' ≃+ C) (f' : A →+ B') (g' : B' →+ C')
    (hf : ∀ a, e (f' a) = f a) (hg : ∀ b, d (g' b) = g (e b))
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g' := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    apply hi
    exact (hf a).symm.trans ((congrArg e h).trans (hf b))
  · intro b
    constructor
    · intro h
      have hz : g (e b) = 0 := (hg b).symm.trans ((congrArg d h).trans (map_zero d))
      obtain ⟨a, ha⟩ := (he (e b)).mp hz
      exact ⟨a, e.injective ((hf a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      apply d.injective
      rw [hg, hf, map_zero]
      exact (he (f a)).mpr ⟨a, rfl⟩
  · intro c
    obtain ⟨b, hb⟩ := hs (d c)
    refine ⟨e.symm b, d.injective ?_⟩
    rw [hg, e.apply_symm_apply]
    exact hb

end SerrePositivity.AlgebraicGeometry
