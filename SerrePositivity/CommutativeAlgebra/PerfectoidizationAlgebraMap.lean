module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor
public import Mathlib.Algebra.Algebra.Hom

/-! # The actual perfectoidization comparison as a map over the original base -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.IsPerfectoidization
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The universal comparison retains the pre-existing algebra structures over R. -/
def mapAlgHom (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) : C →ₐ[R] D where
  __ := IsPerfectoidization.map hf hg q.toRingHom
  commutes' r := by
    have h := RingHom.congr_fun (hf.map_comp hg q.toRingHom) (algebraMap R A r)
    change IsPerfectoidization.map hf hg q.toRingHom (f (algebraMap R A r)) =
      g (q (algebraMap R A r)) at h
    rw [f.commutes, q.commutes, g.commutes] at h
    exact h

/-- Forgetting R-linearity recovers precisely the original functorial ring map. -/
@[simp] theorem mapAlgHom_toRingHom (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) :
    (mapAlgHom hf hg q).toRingHom = IsPerfectoidization.map hf hg q.toRingHom := rfl

/-- The scalar-preserving comparison commutes with the original universal maps. -/
theorem mapAlgHom_comp (hf : IsPerfectoidization p f.toRingHom)
    (hg : IsPerfectoidization p g.toRingHom) (q : A →ₐ[R] B) :
    (mapAlgHom hf hg q).comp f = g.comp q := by
  ext a
  exact RingHom.congr_fun (hf.map_comp hg q.toRingHom) a

/-- Functorial composition retains the same original scalar action. -/
theorem mapAlgHom_mapAlgHom {U E : Type u} [CommRing U] [CommRing E]
    [Algebra R U] [Algebra R E] {h : U →ₐ[R] E}
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (hh : IsPerfectoidization p h.toRingHom)
    (q : A →ₐ[R] B) (r : B →ₐ[R] U) :
    (mapAlgHom hg hh r).comp (mapAlgHom hf hg q) = mapAlgHom hf hh (r.comp q) := by
  ext x
  exact RingHom.congr_fun (hf.map_map hg hh q.toRingHom r.toRingHom) x

end SerrePositivity.IsPerfectoidization
