module

public import SerrePositivity.CommutativeAlgebra.PBasisCompleteLifting
public import SerrePositivity.FieldTheory.PIndependentSet
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 同標数完備局所環の係数体

指定 p-basis の持ち上げを保持する係数写像と、任意剰余体についての存在を構成する。
分数体の分離性・Cohen–Gabber のパラメータはこの結果に含まない。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing

variable {k A : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP A p]

/-- p-basis の存在から、核について完備な全射の切断を構成する。 -/
theorem exists_ringHom_section_of_complete_kernel
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]
    (f : A →+* k) (hf : Function.Surjective f) [IsAdicComplete (RingHom.ker f) A] :
    ∃ g : k →+* A, f.comp g = RingHom.id k := by
  classical
  obtain ⟨s, hs⟩ := exists_pBasis (K := k) (p := p)
  choose β hβ using (fun i : s ↦ hf (i : k))
  obtain ⟨g, hg, _⟩ := hs.existsUnique_ringHom_lift_of_complete_kernel f hf β hβ
  exact ⟨g, hg.1⟩

variable [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]

/-- 剰余体の指定同型を用いて、任意の体 k への表示にも同じ構成を適用する。 -/
theorem IsPBasis.existsUnique_coefficientRingHom_of_residueEquiv {ι : Type*}
    {b : ι → k} (hb : IsPBasis k p b) (e : ResidueField A ≃+* k)
    (β : ι → A) (hβ : ∀ i, e (residue A (β i)) = b i) :
    ∃! g : k →+* A, (e.toRingHom.comp (residue A)).comp g = RingHom.id k ∧
      ∀ i, g (b i) = β i := by
  let f := e.toRingHom.comp (residue A)
  let : IsAdicComplete (RingHom.ker f) A := by
    dsimp [f]
    rw [RingHom.ker_comp_of_injective (residue A) e.injective, ker_residue]
    infer_instance
  exact hb.existsUnique_ringHom_lift_of_complete_kernel f
    (e.surjective.comp residue_surjective) β hβ

/-- 指定した剰余体の p-basis の像を持つ係数写像は一意に存在する。 -/
theorem IsPBasis.existsUnique_coefficientRingHom {ι : Type*} [CharP (ResidueField A) p]
    {b : ι → ResidueField A} (hb : IsPBasis (ResidueField A) p b)
    (β : ι → A) (hβ : ∀ i, residue A (β i) = b i) :
    ∃! g : ResidueField A →+* A,
      (residue A).comp g = RingHom.id (ResidueField A) ∧ ∀ i, g (b i) = β i := by
  let : IsAdicComplete (RingHom.ker (residue A)) A := by
    rw [ker_residue]
    infer_instance
  exact hb.existsUnique_ringHom_lift_of_complete_kernel (residue A) residue_surjective β hβ

/-- 同標数 p の完備局所環は任意剰余体について係数体を持つ。Noether性は不要。 -/
theorem exists_coefficientField_ringHom (p : ℕ) [Fact p.Prime] [CharP A p] :
    ∃ g : ResidueField A →+* A,
      Function.Injective g ∧ IsLocalHom g ∧
        (residue A).comp g = RingHom.id (ResidueField A) := by
  let : CharP (ResidueField A) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero])
  let : IsAdicComplete (RingHom.ker (residue A)) A := by
    rw [ker_residue]
    infer_instance
  obtain ⟨g, hg⟩ := exists_ringHom_section_of_complete_kernel p
    (residue A) residue_surjective
  exact ⟨g, g.injective, inferInstance, hg⟩

end SerrePositivity
