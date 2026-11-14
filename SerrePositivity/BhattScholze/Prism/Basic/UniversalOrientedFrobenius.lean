module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat

/-!
# 普遍向き付き prism の Frobenius の完全平坦性

## 概要
BS 著者版 Example 3.4 の mod p Frobenius は、向きを生成する元について完全平坦。

## 方針
自由環の Frobenius を (p,d) と (p,φ(d)) の剰余で比較する。
局所化の平坦性と完備化の冪零剰余の普遍性を使い、主元の完全平坦性の判定に帰着する。

## 規約
平坦性は mod p Frobenius に沿うスカラー作用を使い、d の像で生成するイデアルについて述べる。

## 使われ方
BS 著者版 Construction 6.1 の底環の性質。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze

open DerivedCompletion
open scoped TensorProduct

private theorem localization_quotient {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
      (S ⧸ I.map (algebraMap R S)) :=
  IsLocalization.isLocalization_of_algEquiv _
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm

private theorem flat_of_localization_square {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (M : Submonoid R) [IsLocalization M R']
    (N : Submonoid S) [IsLocalization N S']
    (f : R →+* S) (g : R' →+* S') (h : g.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hf : f.Flat) : g.Flat := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := g.toAlgebra
  let : Algebra R S' := (g.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  have : IsScalarTower R S S' := .of_algebraMap_eq' h
  have : Module.Flat R S := hf
  have : Module.Flat S S' := IsLocalization.flat S' N
  exact (Module.flat_iff_of_isLocalization R' M S').mpr (Module.Flat.trans R S S')

private def residueMap {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* S) (x : R) :
    (R ⧸ Ideal.span {(p : R), x}) →+* (S ⧸ Ideal.span {(p : S), f x}) :=
  Ideal.quotientMap _ f (by
    rw [Ideal.span_le]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact Ideal.mem_comap.mpr (by rw [map_natCast]; exact Ideal.subset_span (by simp))
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact Ideal.mem_comap.mpr (Ideal.subset_span (by simp)))

private theorem pairIdeal_map {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* S) (x : R) :
    (Ideal.span {(p : R), x}).map f = Ideal.span {(p : S), f x} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast]

private theorem residueMap_flat_localized {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (p : ℕ) (F : R →+* R) (G : S →+* S) (x : R)
    (h : ∀ a, algebraMap R S (F a) = G (algebraMap R S a))
    (hf : (residueMap p F x).Flat) : (residueMap p G (algebraMap R S x)).Flat := by
  let I : Ideal R := Ideal.span {(p : R), x}
  let J : Ideal R := Ideal.span {(p : R), F x}
  let IS := I.map (algebraMap R S)
  let JS := J.map (algebraMap R S)
  let eI : (S ⧸ IS) ≃+* (S ⧸ Ideal.span {(p : S), algebraMap R S x}) :=
    Ideal.quotEquivOfEq (pairIdeal_map p (algebraMap R S) x)
  let eJ : (S ⧸ JS) ≃+* (S ⧸ Ideal.span {(p : S), G (algebraMap R S x)}) :=
    Ideal.quotEquivOfEq ((pairIdeal_map p (algebraMap R S) (F x)).trans (by rw [h]))
  let g := eJ.symm.toRingHom.comp ((residueMap p G (algebraMap R S x)).comp eI.toRingHom)
  have := localization_quotient (S := S) M I
  have := localization_quotient (S := S) M J
  have hg : g.Flat := by
    apply flat_of_localization_square (Algebra.algebraMapSubmonoid (R ⧸ I) M)
      (Algebra.algebraMapSubmonoid (R ⧸ J) M) (residueMap p F x) g _ hf
    apply Ideal.Quotient.ringHom_ext
    ext a
    change g (Ideal.Quotient.mk IS (algebraMap R S a)) =
      Ideal.Quotient.mk JS (algebraMap R S (F a))
    apply eJ.injective
    change eJ (eJ.symm (residueMap p G (algebraMap R S x)
      (eI (Ideal.Quotient.mk IS (algebraMap R S a))))) =
        eJ (Ideal.Quotient.mk JS (algebraMap R S (F a)))
    rw [RingEquiv.apply_symm_apply]
    change Ideal.Quotient.mk _ (G (algebraMap R S a)) =
      Ideal.Quotient.mk _ (algebraMap R S (F a))
    rw [h a]
  have hi : eI.symm.toRingHom.Flat := RingHom.Flat.of_bijective eI.symm.bijective
  have hj : eJ.toRingHom.Flat := RingHom.Flat.of_bijective eJ.bijective
  have ht := (hi.comp hg).comp hj
  have he : (eJ.toRingHom.comp (g.comp eI.symm.toRingHom)) =
      residueMap p G (algebraMap R S x) := by
    apply RingHom.ext
    intro a
    change eJ (eJ.symm (residueMap p G (algebraMap R S x) (eI (eI.symm a)))) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact he ▸ ht

private theorem complete_of_pow_eq_zero {R : Type u} [CommRing R] (x : R) (n : ℕ)
    (h : x ^ n = 0) : IsModuleComplete R x (ModuleCat.of R R) := by
  apply isModuleComplete_of_pow_smul_zero R x _ n
  simp [h]

private def completionResidueEquiv {R : Type u} [CommRing R]
    (p : ℕ) (d : R) (I : Ideal R) (hp : (p : R) ∈ I) (n : ℕ) (hd : d ^ n ∈ I) :
    letI := pdCompletionCommRing R p d
    {e : (R ⧸ I) ≃+* (PDCompletionH0 R p d ⧸ I.map (pdCompletionUnit R p d)) //
      ∀ a, e (Ideal.Quotient.mk I a) =
        Ideal.Quotient.mk _ (pdCompletionUnit R p d a)} := by
  letI := pdCompletionCommRing R p d
  let C : Type u := PDCompletionH0 R p d
  let j := pdCompletionUnit R p d
  let J := I.map j
  let q := Ideal.Quotient.mk I
  let q' := Ideal.Quotient.mk J
  let g := Ideal.quotientMap J j Ideal.le_comap_map
  have hpq : q (p : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hdq : q d ^ n = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hd
  let H := existsUnique_pdCompletionRingHom R p d (R ⧸ I) q
    (complete_of_pow_eq_zero (p : R ⧸ I) 1 (by simpa only [pow_one, map_natCast] using hpq))
    (complete_of_pow_eq_zero _ _ hdq)
  let f := H.choose
  have hf' (a : R) : f (j a) = q a := DFunLike.congr_fun H.choose_spec.1 a
  let f' := Ideal.Quotient.lift J f (by
    have hJ : J ≤ RingHom.ker f := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change f (j a) = 0
      rw [hf']
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact fun _ ha ↦ hJ ha)
  have hfg : f'.comp g = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact hf' a
  have hgf : g.comp f' = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    change g.comp f = q'
    have hp' : q' (j (p : R)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem j hp)
    have hd' : q' (j d) ^ n = 0 := by
      rw [← map_pow, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem j hd)
    apply pdCompletionRingHom_ext R p d (C ⧸ J) (q'.comp j)
      (complete_of_pow_eq_zero (p : C ⧸ J) 1 (by simpa only [pow_one, map_natCast] using hp'))
      (complete_of_pow_eq_zero _ _ hd')
    · ext a
      change g (f (j a)) = q' (j a)
      rw [hf']
      rfl
    · rfl
  exact ⟨RingEquiv.ofRingHom g f' hgf hfg, fun a ↦ rfl⟩

private theorem residueMap_flat_completed {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    (D : DeltaStructure p R) (d : R) (hflat : (residueMap p D.frobeniusLift d).Flat) :
    let := pdCompletionCommRing R p d
    (residueMap p (deltaPDCompletionStructure D d).frobeniusLift
      (pdCompletionUnit R p d d)).Flat := by
  let := pdCompletionCommRing R p d
  let j := pdCompletionUnit R p d
  let F := D.frobeniusLift
  let G := (deltaPDCompletionStructure D d).frobeniusLift
  have hj := (pdCompletionUnit_isDeltaHom D d).map_frobeniusLift
  let I : Ideal R := Ideal.span {(p : R), d}
  let J : Ideal R := Ideal.span {(p : R), F d}
  have hpI : (p : R) ∈ I := Ideal.subset_span (by simp)
  have hpJ : (p : R) ∈ J := Ideal.subset_span (by simp)
  have hdI : d ^ 1 ∈ I := by
    rw [pow_one]
    exact Ideal.subset_span (by simp)
  have hdJ : d ^ p ∈ J := by
    have hF : F d ∈ J := Ideal.subset_span (by simp)
    have hδ : (p : R) * D.delta d ∈ J := J.mul_mem_right _ hpJ
    simpa only [F, DeltaStructure.frobeniusLift_apply, add_sub_cancel_right] using J.sub_mem hF hδ
  let e := completionResidueEquiv p d I hpI 1 hdI
  let e' := completionResidueEquiv p d J hpJ p hdJ
  let eI := e.val.trans (Ideal.quotEquivOfEq (pairIdeal_map p j d))
  let eJ := e'.val.trans (Ideal.quotEquivOfEq ((pairIdeal_map p j (F d)).trans (by rw [hj])))
  have heI (a : R) : eI (Ideal.Quotient.mk I a) = Ideal.Quotient.mk _ (j a) := by
    rw [RingEquiv.trans_apply, e.property, Ideal.quotEquivOfEq_mk]
  have heJ (a : R) : eJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk _ (j a) := by
    rw [RingEquiv.trans_apply, e'.property, Ideal.quotEquivOfEq_mk]
  let f := residueMap p F d
  let g := residueMap p G (j d)
  have hcomm : g.comp eI.toRingHom = eJ.toRingHom.comp f := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    change g (eI (Ideal.Quotient.mk I a)) = eJ (Ideal.Quotient.mk J (F a))
    rw [heI, heJ, hj]
    rfl
  have hI : eI.symm.toRingHom.Flat := RingHom.Flat.of_bijective eI.symm.bijective
  have hJ : eJ.toRingHom.Flat := RingHom.Flat.of_bijective eJ.bijective
  have hG : g = (eJ.toRingHom.comp f).comp eI.symm.toRingHom := by
    rw [← hcomm]
    apply RingHom.ext
    intro a
    change g a = g (eI (eI.symm a))
    rw [RingEquiv.apply_symm_apply]
  change g.Flat
  rw [hG]
  exact hI.comp (hflat.comp hJ)

private def pairResidueEquiv {R : Type u} [CommRing R] (p : ℕ) (d : R) :
    (R ⧸ Ideal.span {(p : R), d}) ≃+*
      ((R ⧸ Ideal.span {(p : R)}) ⧸ Ideal.span {Ideal.Quotient.mk _ d}) :=
  (Ideal.quotEquivOfEq (Ideal.span_insert (p : R) {d})).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(p : R)}) (Ideal.span {d})).symm.trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])))

private theorem pairResidueEquiv_mk {R : Type u} [CommRing R] (p : ℕ) (d a : R) :
    pairResidueEquiv p d (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a) := by
  rw [pairResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  rfl

private theorem modPrimeFrobenius_completelyFlat_of_residueFlat {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] (D : DeltaStructure p R) (d : R)
    (hd : IsSMulRegular (ModP R p) (Ideal.Quotient.mk (Ideal.span {(p : R)}) d))
    (hflat : (residueMap p D.frobeniusLift d).Flat) :
    IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : R)}) d})
      (baseChangeScalarModule (modPMap p D.frobeniusLift)) := by
  let φ := modPMap p D.frobeniusLift
  let Q := ModP R p
  let q : R →+* Q := Ideal.Quotient.mk _
  let a := q d
  let I := Ideal.span {a}
  let T := ULift.{0} Q
  let eT : T ≃+* Q := ULift.ringEquiv
  let A : Algebra Q T := (eT.symm.toRingHom.comp φ).toAlgebra
  let : Algebra Q T := A
  let : Module Q T := A.toModule
  let : SMul Q T := A.toModule.toSMul
  apply isCompletelyFlat_of_linearEquiv I
    (M := T) (N := baseChangeScalarModule φ)
    { eT.toAddEquiv with
      map_smul' := by
        intro r x
        change eT (r • x) = φ r * eT x
        rw [Algebra.smul_def, map_mul]
        rfl }
  have hφ : φ a = a ^ p :=
    D.map_frobeniusLift_of_map_p_eq_zero q (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))) d
  have hreg : IsSMulRegular T a := by
    intro x y hxy
    apply eT.injective
    apply hd.pow p
    change a ^ p * eT x = a ^ p * eT y
    rw [← hφ]
    change (algebraMap Q T a) * x = (algebraMap Q T a) * y at hxy
    have h := congrArg (fun z : T ↦ eT z) hxy
    simpa only [map_mul, show eT (algebraMap Q T a) = φ a from rfl] using h
  apply isCompletelyFlat_principal_of_regular a hd T hreg
  let e := pairResidueEquiv p d
  let e' := pairResidueEquiv p (D.frobeniusLift d)
  let J := I.map (algebraMap Q T)
  have hI : J = (Ideal.span {q (D.frobeniusLift d)}).map eT.symm.toRingHom := by
    change I.map (algebraMap Q T) = _
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    rfl
  let eJ := e'.trans (Ideal.quotientEquiv _ J eT.symm hI)
  let g := algebraMap (Q ⧸ I) (T ⧸ J)
  have hcomm : g.comp e.toRingHom = eJ.toRingHom.comp (residueMap p D.frobeniusLift d) := by
    apply Ideal.Quotient.ringHom_ext
    ext b
    change g (e (Ideal.Quotient.mk _ b)) = eJ (Ideal.Quotient.mk _ (D.frobeniusLift b))
    rw [pairResidueEquiv_mk]
    rfl
  have hG : g = (eJ.toRingHom.comp (residueMap p D.frobeniusLift d)).comp e.symm.toRingHom := by
    rw [← hcomm]
    apply RingHom.ext
    intro b
    change g b = g (e (e.symm b))
    rw [RingEquiv.apply_symm_apply]
  have hg : g.Flat := by
    rw [hG]
    exact (RingHom.Flat.of_bijective e.symm.bijective).comp
      (hflat.comp (RingHom.Flat.of_bijective eJ.bijective))
  have : Module.Flat (Q ⧸ I) (T ⧸ J) := RingHom.flat_algebraMap_iff.mp hg
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I).symm.toLinearEquiv

/-- 概要：普遍向き付き prism の mod p Frobenius は d 完全平坦。
方針：自由 δ 環の剰余 Frobenius の平坦性を局所化と完備化で移し、主元の判定を使う。
規約：BS 著者版 Example 3.4。加群は mod p Frobenius に沿う代数構造を持つ。
使われ方：普遍向き付き prism を起点とする係数比較。 -/
theorem universalOrientedPrism_frobenius_isCompletelyFlat (p : ℕ) [Fact p.Prime] :
    let U := UniversalOrientedPrismRing.{u} p
    let P := universalOrientedPrism.{u} p
    IsCompletelyFlat (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : U)}) P.generator})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)) := by
  let x : FreeDeltaRing PUnit.{u+1} := freeDistinguishedGenerator
  let F := freeDeltaStructure p PUnit.{u+1}
  let L := UniversalDistinguishedRing.{u} p
  let d := universalDistinguishedGenerator.{u} p
  let G := universalDistinguishedDelta.{u} p
  have hfree : (residueMap p F.frobeniusLift x).Flat := by
    have hF : F.frobeniusLift = freeDeltaFrobenius p PUnit.{u+1} :=
      freeDeltaStructure_frobeniusLift p PUnit.{u+1}
    rw [hF]
    have he : residueMap p (freeDeltaFrobenius p PUnit.{u+1}) x =
        freeDeltaFrobeniusCoordinateResidueMap p PUnit.{u+1} PUnit.unit := by
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro a
      exact (freeDeltaFrobeniusCoordinateResidueMap_mk p PUnit.{u+1} PUnit.unit a).symm
    rw [he]
    exact (freeDeltaFrobeniusCoordinateResidueMap_faithfullyFlat p PUnit.{u+1} PUnit.unit).flat
  have hloc : (residueMap p G.frobeniusLift d).Flat :=
    residueMap_flat_localized (S := L) (F.frobeniusDenominators (distinguishedDenominators p))
      p F.frobeniusLift G.frobeniusLift x
      (universalDistinguished_algebraMap_isDeltaHom p).map_frobeniusLift hfree
  exact modPrimeFrobenius_completelyFlat_of_residueFlat _ _
    (universalOrientedPrism_regular p).2 (residueMap_flat_completed G d hloc)

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 3.4"] _root_.SerrePositivity.BhattScholze.universalOrientedPrism_frobenius_isCompletelyFlat
