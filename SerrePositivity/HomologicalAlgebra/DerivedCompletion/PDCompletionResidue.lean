module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 二元完備化の主剰余

## 概要
(p,d) 完備化を d で割ると、d で割った環の p 完備化になる。

## 方針
両辺を p 完備な剰余環への反映として比較する。

## 使われ方
完備自由 δ 環の剰余を、多項式環の p 完備化として計算する。
-/

public noncomputable section

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (p : ℕ) (d : R)

private theorem natCast_complete_restrict {B T : Type u} [CommRing B] [CommRing T]
    (p : ℕ) (f : B →+* T) (h : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    let := f.toAlgebra
    IsModuleComplete B (p : B) (ModuleCat.of B T) := by
  let := f.toAlgebra
  apply (isModuleComplete_algebraMap_iff B T (p : B) T).mp
  change IsModuleComplete T (f (p : B)) (ModuleCat.of T T)
  rwa [map_natCast]

private def pdCompletionResidueComparison :
    let := pdCompletionCommRing R p d
    let := principalCompletionCommRing (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
    let Q := R ⧸ Ideal.span {d}
    let q := Ideal.Quotient.mk (Ideal.span {d})
    let ι := pdCompletionUnit R p d
    let π := Ideal.Quotient.mk (Ideal.span {ι d})
    {e : (PDCompletionH0 R p d ⧸ Ideal.span {ι d}) ≃+*
      PrincipalCompletionH0 Q (p : Q) //
      e.toRingHom.comp (π.comp ι) = (principalCompletionUnitRingHom Q (p : Q)).comp q} := by
  let C := PDCompletionH0 R p d
  let : CommRing C := pdCompletionCommRing R p d
  let Q := R ⧸ Ideal.span {d}
  let D := PrincipalCompletionH0 Q (p : Q)
  let : CommRing D := principalCompletionCommRing Q (p : Q)
  let ι : R →+* C := pdCompletionUnit R p d
  let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {d})
  let j : Q →+* D := principalCompletionUnitRingHom Q (p : Q)
  let E := C ⧸ Ideal.span {ι d}
  let π : C →+* E := Ideal.Quotient.mk (Ideal.span {ι d})
  have hq : q d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hπ : π (ι d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hD : IsModuleComplete D (p : D) (ModuleCat.of D D) := by
    let : Module Q D := inferInstance
    let : Algebra Q D := principalCompletionAlgebra Q (p : Q)
    have h := (isModuleComplete_algebraMap_iff Q D (p : Q) D).mpr
      (principalCompletionH0_isModuleComplete Q (p : Q))
    change IsModuleComplete D (j (p : Q)) (ModuleCat.of D D) at h
    have hj : j (p : Q) = (p : D) := map_natCast j p
    exact hj ▸ h
  have hC : IsModuleComplete C (p : C) (ModuleCat.of C C) := by
    let : Algebra R C := ι.toAlgebra
    let : Module R C := ι.toAlgebra.toModule
    have h := (isModuleComplete_algebraMap_iff R C (p : R) C).mpr
      (pdCompletionH0_isComplete_p R p d)
    change IsModuleComplete C (ι (p : R)) (ModuleCat.of C C) at h
    simpa only [map_natCast] using h
  have hE : IsModuleComplete E (p : E) (ModuleCat.of E E) :=
    isModuleComplete_principal_quotient_natCast C p (ι d) hC
  have hd : let := (j.comp q).toAlgebra; IsModuleComplete R d (ModuleCat.of R D) := by
    let := (j.comp q).toAlgebra
    apply (isModuleComplete_algebraMap_iff R D d D).mp
    change IsModuleComplete D (j (q d)) (ModuleCat.of D D)
    rw [hq, map_zero]
    exact isModuleComplete_of_pow_smul_zero D 0 _ 1 (by intro x; simp)
  let F := pdCompletion_existsUnique_ringHom R p d D (j.comp q)
    (natCast_complete_restrict p _ hD) hd
  let f : C →+* D := F.choose
  have hf : f.comp ι = j.comp q := F.choose_spec.1
  have hf0 : f (ι d) = 0 := by
    rw [show f (ι d) = j (q d) from RingHom.congr_fun hf d, hq, map_zero]
  let f' : E →+* D := Ideal.Quotient.lift (Ideal.span {ι d}) f
    (fun x hx => ((Ideal.span_singleton_le_iff_mem (RingHom.ker f)).mpr hf0) hx)
  have hf' : f'.comp π = f := rfl
  let k : Q →+* E := Ideal.Quotient.lift (Ideal.span {d}) (π.comp ι)
    (fun x hx => ((Ideal.span_singleton_le_iff_mem (RingHom.ker (π.comp ι))).mpr hπ) hx)
  have hk : k.comp q = π.comp ι := rfl
  let G := principalCompletion_existsUnique_ringHom Q (p : Q) E k
    (natCast_complete_restrict p _ hE)
  let g : D →+* E := G.choose
  have hg : g.comp j = k := G.choose_spec.1
  have hfg : f'.comp g = RingHom.id D := by
    have hu := principalCompletion_existsUnique_ringHom Q (p : Q) D j
      (natCast_complete_restrict p _ hD)
    refine hu.unique (y₁ := f'.comp g) (y₂ := RingHom.id D) ?_ ?_
    · change (f'.comp g).comp j = j
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro x
      change f' (g (j (q x))) = j (q x)
      rw [show g (j (q x)) = k (q x) from RingHom.congr_fun hg (q x),
        show k (q x) = π (ι x) from RingHom.congr_fun hk x,
        show f' (π (ι x)) = f (ι x) from RingHom.congr_fun hf' (ι x)]
      exact RingHom.congr_fun hf x
    · change (RingHom.id D).comp j = j
      exact RingHom.id_comp j
  have hgf : g.comp f' = RingHom.id E := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hf', RingHom.id_comp]
    have hz : let := (π.comp ι).toAlgebra; IsModuleComplete R d (ModuleCat.of R E) := by
      let := (π.comp ι).toAlgebra
      apply (isModuleComplete_algebraMap_iff R E d E).mp
      change IsModuleComplete E (π (ι d)) (ModuleCat.of E E)
      rw [hπ]
      exact isModuleComplete_of_pow_smul_zero E 0 _ 1 (by intro x; simp)
    have hu := pdCompletion_existsUnique_ringHom R p d E (π.comp ι)
      (natCast_complete_restrict p _ hE) hz
    apply hu.unique ?_ rfl
    rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hg, hk]
  refine ⟨RingEquiv.ofRingHom f' g hfg hgf, ?_⟩
  change f'.comp (π.comp ι) = j.comp q
  rw [← RingHom.comp_assoc, hf', hf]

/-- (p,d) 完備化の d 剰余は、d 剰余の p 完備化。 -/
def pdCompletionResidueEquiv :
    let := pdCompletionCommRing R p d
    let := principalCompletionCommRing (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
    (PDCompletionH0 R p d ⧸ Ideal.span {pdCompletionUnit R p d d}) ≃+*
      PrincipalCompletionH0 (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d}) :=
  (pdCompletionResidueComparison R p d).val

/-- 剰余の比較同型は二つの完備化の単位を結ぶ。 -/
theorem pdCompletionResidueEquiv_unit (x : R) :
    let := pdCompletionCommRing R p d
    let := principalCompletionCommRing (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
    pdCompletionResidueEquiv R p d (Ideal.Quotient.mk _ (pdCompletionUnit R p d x)) =
      principalCompletionUnitRingHom (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
        (Ideal.Quotient.mk _ x) :=
  RingHom.congr_fun (pdCompletionResidueComparison R p d).property x

end SerrePositivity.DerivedCompletion
