module

public import SerrePositivity.CommutativeAlgebra.PBasisFrobeniusLift
public import SerrePositivity.CommutativeAlgebra.FrobeniusCoefficientLift
public import SerrePositivity.FieldTheory.PBasisRingHomExt
public import SerrePositivity.CommutativeAlgebra.PBasisNilpotentLifting

/-! # 冪零核に沿う指定 p-basis の持ち上げの存在

係数の Frobenius 持ち上げから冪関係を導き、k 全体の環写像と剰余写像との両立を構成する。
完備環への逆極限はここでは扱わない。
-/

@[expose] public section
namespace SerrePositivity

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP A p] {b : ι → k}

/-- 任意の指定持ち上げに対して、冪零核を持つ全射の環切断が存在する。 -/
theorem IsPBasis.exists_ringHom_lift_of_nilpotent_kernel (hb : IsPBasis k p b)
    (f : A →+* k) (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f))
    (β : ι → A) (hβ : ∀ i, f (β i) = b i) :
    ∃ g : k →+* A, f.comp g = RingHom.id k ∧ ∀ i, g (b i) = β i := by
  obtain ⟨n, c, hc, hp⟩ := exists_frobeniusCoefficientLift_of_nilpotent_kernel p f hf hker
  have hpow : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i)) := by
    intro i
    simpa only [hβ i] using (hp (β i)).symm
  obtain ⟨g, hg, hgb⟩ := hb.exists_ringHom_prescribed_of_frobeniusRelations n c β hpow
  refine ⟨g, ?_, hgb⟩
  refine hb.ringHom_ext_of_eq_pow_exp (f.comp g) (RingHom.id k) (fun i ↦ ?_) n (fun x ↦ ?_)
  · change f (g (b i)) = b i
    rw [hgb, hβ]
  · change f (g (x ^ p ^ n)) = x ^ p ^ n
    have h := hg (frobeniusPowerEquiv k p n x)
    change g (x ^ p ^ n) = c (frobeniusPowerEquiv k p n x) at h
    rw [h]
    exact RingHom.congr_fun hc (frobeniusPowerEquiv k p n x)

/-- 指定 p-basis の像を持つ切断は、冪零核の下で存在して一意。 -/
theorem IsPBasis.existsUnique_ringHom_lift_of_nilpotent_kernel (hb : IsPBasis k p b)
    (f : A →+* k) (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f))
    (β : ι → A) (hβ : ∀ i, f (β i) = b i) :
    ∃! g : k →+* A, f.comp g = RingHom.id k ∧ ∀ i, g (b i) = β i := by
  obtain ⟨g, hg, hgb⟩ := hb.exists_ringHom_lift_of_nilpotent_kernel f hf hker β hβ
  refine ⟨g, ⟨hg, hgb⟩, ?_⟩
  intro l hl
  exact hb.ringHom_lift_unique_of_nilpotent_kernel f hker l g (hl.1.trans hg.symm)
    (fun i ↦ (hl.2 i).trans (hgb i).symm)

end SerrePositivity
