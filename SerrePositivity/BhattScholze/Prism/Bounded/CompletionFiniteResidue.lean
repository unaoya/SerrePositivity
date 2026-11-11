module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 二元完備化の有限剰余

## 概要
二つの座標の冪を含むイデアルでの通常の剰余は、完備化の標準写像で保たれる。

## 方針
二つの剰余環で座標の作用は冪零なので、環の射を実完備化から一意に延長する。

## 規約
通常の剰余環と導来完備化の H⁰ を比較する。座標の正則性は不要。

## 使われ方
BS 著者版 Corollary 3.12 の完備 Čech 複体の有限剰余。
-/

public noncomputable section

universe u

namespace SerrePositivity.DerivedCompletion

variable {R : Type u} [CommRing R]

/-- 概要：二つの座標の冪を含むイデアルによる剰余は、標準完備化写像で変わらない。
方針：双方の剰余への射を商と完備化の普遍性で比較する。
規約：通常の環同型で、元の代表元を保つ。
使われ方：完備テンソル積を有限剰余で通常のテンソル積と比較する。 -/
theorem exists_pdCompletion_finiteResidue_equiv (p : ℕ) (d : R) (I : Ideal R)
    (m n : ℕ) (hp : (p : R) ^ m ∈ I) (hd : d ^ n ∈ I) :
    letI := pdCompletionCommRing R p d
    let u := pdCompletionUnit R p d
    ∃ e : (PDCompletionH0 R p d ⧸ I.map u) ≃+* (R ⧸ I),
      (e.toRingHom.comp (Ideal.Quotient.mk (I.map u))).comp u = Ideal.Quotient.mk I := by
  let := pdCompletionCommRing R p d
  let H := PDCompletionH0 R p d
  let u := pdCompletionUnit R p d
  let J := I.map u
  let q := Ideal.Quotient.mk I
  let r := Ideal.Quotient.mk J
  have complete_of_mem {T : Type u} [CommRing T] (f : R →+* T)
      (hf : I ≤ RingHom.ker f) {a : R} (k : ℕ) (ha : a ^ k ∈ I) :
      letI := f.toAlgebra
      IsModuleComplete R a (ModuleCat.of R T) := by
    let := f.toAlgebra
    apply isModuleComplete_of_pow_smul_zero R a _ k
    intro x
    change f (a ^ k) * x = 0
    rw [show f (a ^ k) = 0 from hf ha, zero_mul]
  have hq : I ≤ RingHom.ker q := fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hr : I ≤ RingHom.ker (r.comp u) := fun _ hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem u hx)
  obtain ⟨f, hf, _⟩ := pdCompletion_existsUnique_ringHom R p d (R ⧸ I) q
    (complete_of_mem q hq m hp) (complete_of_mem q hq n hd)
  let g : R ⧸ I →+* H ⧸ J := Ideal.Quotient.lift I (r.comp u) fun _ hx ↦ hr hx
  have hfJ : J ≤ RingHom.ker f := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change (f.comp u) a = 0
    rw [hf]
    exact hq ha
  let f' : H ⧸ J →+* R ⧸ I := Ideal.Quotient.lift J f fun _ hx ↦ hfJ hx
  have hg : g.comp q = r.comp u := rfl
  have hf' : f'.comp r = f := rfl
  have hleft : f'.comp g = RingHom.id (R ⧸ I) := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hg, ← RingHom.comp_assoc, hf', hf, RingHom.id_comp]
  have hright : g.comp f' = RingHom.id (H ⧸ J) := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hf', RingHom.id_comp]
    obtain ⟨k, _, hk⟩ := pdCompletion_existsUnique_ringHom R p d (H ⧸ J) (r.comp u)
      (complete_of_mem (r.comp u) hr m hp) (complete_of_mem (r.comp u) hr n hd)
    exact (hk (g.comp f) (by
      change (g.comp f).comp u = r.comp u
      rw [RingHom.comp_assoc, hf, hg])).trans (hk r rfl).symm
  refine ⟨RingEquiv.ofRingHom f' g hleft hright, ?_⟩
  change (f'.comp r).comp u = q
  rw [hf', hf]

end SerrePositivity.DerivedCompletion
