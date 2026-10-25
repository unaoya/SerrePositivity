module

public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorPerfectoidUniversal
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # Ring-perfectoidization of a general tensor diagram

This is the ring-valued pushout statement underlying author-version BS Prop.
8.13. The three specified perfectoidizations form a compatible diagram. Its
completed tensor is supplied by the existing perfectoid tensor theorem, rather
than by rebuilding prismatic cohomology or its symmetric monoidal structure.
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R S T P C D : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing P] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R T] [Algebra P C] [Algebra P D]
    (r : R →+* P) (s : S →+* C) (t : T →+* D)
    (hs : ∀ x, s (algebraMap R S x) = algebraMap P C (r x))
    (ht : ∀ x, t (algebraMap R T x) = algebraMap P D (r x))

/-- The ordinary tensor map of the original diagram into the tensor of its
specified perfectoidizations, balanced over the specified new base. -/
def perfectoidizationTensorDiagramMap : S ⊗[R] T →+* C ⊗[P] D :=
  coefficientTensorLift
    ((Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).toRingHom.comp s)
    ((Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).toRingHom.comp t)
    (fun x => by
      change (Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D)
          (s (algebraMap R S x)) =
        (Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D)
          (t (algebraMap R T x))
      rw [hs, ht]
      exact ((Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).commutes (r x)).trans
        ((Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).commutes (r x)).symm)

/-- The diagram map retains both specified factor maps on every pure tensor. -/
lemma perfectoidizationTensorDiagramMap_tmul (x : S) (y : T) :
    perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y) = s x ⊗ₜ[P] t y := by
  change (s x ⊗ₜ[P] (1 : D)) * ((1 : C) ⊗ₜ[P] t y) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable (p : ℕ) [Fact p.Prime]

/-- The tensor of three compatible ring-perfectoidizations is universal among
perfectoid targets. No flatness, completeness, or surjectivity of the original
diagram is needed for this ring-valued universal property. -/
lemma perfectoidizationTensorDiagramMap_isPerfectoidization
    (hr : IsPerfectoidization p r) (hsp : IsPerfectoidization p s)
    (htp : IsPerfectoidization p t) (E : Type u) [CommRing E]
    (f : C ⊗[P] D →+* E) (hf : IsPerfectoidization p f) :
    IsPerfectoidization p (f.comp (perfectoidizationTensorDiagramMap r s t hs ht)) := by
  let iC := (Algebra.TensorProduct.includeLeft : C →ₐ[P] C ⊗[P] D).toRingHom
  let iD := (Algebra.TensorProduct.includeRight : D →ₐ[P] C ⊗[P] D).toRingHom
  let jS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom
  let jT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  refine ⟨hf.1, ?_⟩
  intro U _ hU g
  obtain ⟨lC, hlC, huniqC⟩ := hsp.2 U hU (g.comp jS)
  obtain ⟨lD, hlD, huniqD⟩ := htp.2 U hU (g.comp jT)
  have hbase : lC.comp (algebraMap P C) = lD.comp (algebraMap P D) := by
    apply (hr.2 U hU ((lC.comp (algebraMap P C)).comp r)).unique rfl
    ext x
    change lD (algebraMap P D (r x)) = lC (algebraMap P C (r x))
    rw [← hs, ← ht]
    calc
      lD (t (algebraMap R T x)) = g (jT (algebraMap R T x)) :=
        RingHom.congr_fun hlD _
      _ = g (jS (algebraMap R S x)) := congrArg g
        (((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes x).trans
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes x).symm)
      _ = lC (s (algebraMap R S x)) := (RingHom.congr_fun hlC _).symm
  let k : C ⊗[P] D →+* U := coefficientTensorLift lC lD (RingHom.congr_fun hbase)
  obtain ⟨l, hl, huniq⟩ := hf.2 U hU k
  have hlg : l.comp (f.comp (perfectoidizationTensorDiagramMap r s t hs ht)) = g := by
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
    · change l (f (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] y))) =
        g (x ⊗ₜ[R] y)
      rw [perfectoidizationTensorDiagramMap_tmul]
      have hh := RingHom.congr_fun hl (s x ⊗ₜ[P] t y)
      change l (f (s x ⊗ₜ[P] t y)) = lC (s x) * lD (t y) at hh
      have hc : lC (s x) = g (jS x) := RingHom.congr_fun hlC x
      have hd : lD (t y) = g (jT y) := RingHom.congr_fun hlD y
      rw [hh, hc, hd, ← map_mul]
      congr 1
      change (x ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · simp only [map_add, hx, hy]
  refine ⟨l, hlg, ?_⟩
  intro m hm
  have hmC : (m.comp (f.comp iC)).comp s = g.comp jS := by
    ext x
    have hh := RingHom.congr_fun hm (x ⊗ₜ[R] (1 : T))
    change m (f (perfectoidizationTensorDiagramMap r s t hs ht (x ⊗ₜ[R] 1))) = _ at hh
    rw [perfectoidizationTensorDiagramMap_tmul, map_one] at hh
    exact hh
  have hmD : (m.comp (f.comp iD)).comp t = g.comp jT := by
    ext y
    have hh := RingHom.congr_fun hm ((1 : S) ⊗ₜ[R] y)
    change m (f (perfectoidizationTensorDiagramMap r s t hs ht (1 ⊗ₜ[R] y))) = _ at hh
    rw [perfectoidizationTensorDiagramMap_tmul, map_one] at hh
    exact hh
  have heC : m.comp (f.comp iC) = lC := huniqC _ hmC
  have heD : m.comp (f.comp iD) = lD := huniqD _ hmD
  apply huniq
  apply RingHom.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y => ?_) (fun x y hx hy => ?_)
  · have hxy : x ⊗ₜ[P] y = iC x * iD y := by
      change x ⊗ₜ[P] y = (x ⊗ₜ[P] (1 : D)) * ((1 : C) ⊗ₜ[P] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change m (f (x ⊗ₜ[P] y)) = lC x * lD y
    have hc : m (f (iC x)) = lC x := RingHom.congr_fun heC x
    have hd : m (f (iD y)) = lD y := RingHom.congr_fun heD y
    rw [hxy, map_mul, map_mul, hc, hd]
  · simp only [map_add, hx, hy]

end SerrePositivity.BhattScholze
