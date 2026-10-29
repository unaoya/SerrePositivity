module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Field.Equiv
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # 単生成の剰余体拡大の持ち上げ

## 概要

局所環 `B` と、剰余体 `k = B/m_B` 上の体 `K` を考える。`K` の一元 `a` で生成される拡大 `k(a)` を、
平坦局所拡大 `B → C` で `m_B C = m_C` かつ剰余体が `k(a)` となるもので実現する
（`exists_flat_local_extension_of_simple_generator`）。剰余体の拡大の後続段として図式に組み込む形が
`exists_residueField_successor`。有限生成（本質的有限型）の剰余体拡大も、これを繰り返して実現する
（`exists_complete_flat_local_extension_of_fg` など。超限構成は使わない）。

## 方針

- 代数的な場合：`a` の最小多項式をモニックに持ち上げた `F` で `C = B[X]/(F)` とする。
  `C` は有限自由で、閉ファイバーは `k[X]/(F̄) = k(a)`（体）なので `C` は局所
  （`adjoinRoot_isLocalRing_of_irreducible_reduction`）。
- 超越的な場合：`K = k(a)` への評価写像の核で `B[X]` を局所化する。超越性から核は `m_B B[X]` に等しい。
- 完備化（`ResidueFieldCompletion`）：指定した剰余体を保ったまま Noether 局所拡大を完備化する。

## 規約

分離性は仮定しない（純非分離の既約多項式も含む）。剰余体の同一視は、`K` への体の埋め込みとして保持する。

## 使われ方

剰余体拡大の超限構成の後続段（`ResidueFieldExtension/Limit`・`Step`）。有限生成版は現在使われていないが、
超限構成を要しない形で Mathlib に出すときの最初の段として残す（mathlib-upstream の G8）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section Construction

open IsLocalRing

/-- 整拡大の閉ファイバーが体なら、拡大環は局所環である。
各極大イデアルの収縮が基底の極大イデアルなので、閉ファイバーの極大イデアルが唯一となる。 -/
theorem isLocalRing_of_integral_of_field_closedFibre
    (B S : Type*) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S))) : IsLocalRing S := by
  let J := (maximalIdeal B).map (algebraMap B S)
  have hJ : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, fun P hP ↦ ?_⟩
  have hc : P.comap (algebraMap B S) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap B S) (fun s ↦ Algebra.IsIntegral.isIntegral s) P)
  exact (hJ.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.mpr hc.ge)).symm

/-- 閉ファイバーが体なら、拡大した極大イデアルは終域の極大イデアルに等しい。
終域の局所性を別途供給すれば、整性やNoether性はこの同定に不要。 -/
theorem maximalIdeal_map_eq_of_field_closedFibre
    (B S : Type*) [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S]
    (hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S))) :
    (maximalIdeal B).map (algebraMap B S) = maximalIdeal S :=
  IsLocalRing.eq_maximalIdeal
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfield)

/-- 多項式を加えた代数の閉ファイバーは、剰余体上で同じ多項式を加えた代数である。
基底環上の代数同型として構成し、係数写像との両立を保持する。 -/
noncomputable def adjoinRoot_closedFibreEquiv
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) :
    (AdjoinRoot F ⧸ (maximalIdeal B).map (algebraMap B (AdjoinRoot F))) ≃ₐ[B]
      AdjoinRoot (F.map (residue B)) :=
  AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)

/-- 閉ファイバー同型は、持ち上げた根を還元多項式の根へ送る。 -/
@[simp] theorem adjoinRoot_closedFibreEquiv_root
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) :
    adjoinRoot_closedFibreEquiv F (Ideal.Quotient.mk _ (AdjoinRoot.root F)) =
      AdjoinRoot.root (F.map (residue B)) := by
  have h := AdjoinRoot.quotEquivQuotMap_apply_mk F Polynomial.X (maximalIdeal B)
  rw [Polynomial.map_X] at h
  -- 剰余体と商、AdjoinRootと多項式商の定義上の同一視を、この適用だけで展開する。
  with_unfolding_all exact h

/-- 剰余体で既約になるモニック多項式の商は局所環である。
純非分離の既約多項式も含め、分離性は仮定しない。 -/
theorem adjoinRoot_isLocalRing_of_irreducible_reduction
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) (hF : F.Monic)
    (hirr : Irreducible (F.map (residue B))) : IsLocalRing (AdjoinRoot F) := by
  let : Algebra.IsIntegral B (AdjoinRoot F) := AdjoinRoot.isIntegral_of_monic hF
  let : Fact (Irreducible (F.map (residue B))) := ⟨hirr⟩
  let : Field (AdjoinRoot (F.map (residue B))) := inferInstance
  apply isLocalRing_of_integral_of_field_closedFibre B (AdjoinRoot F)
  exact MulEquiv.isField (Field.toIsField _) (adjoinRoot_closedFibreEquiv F).toRingEquiv.toMulEquiv

end Construction

section Completion

open IsLocalRing

/-- 平坦Noether局所拡大を完備化し、指定剰余体と生成元の対応を移送する。
Noether性を要求するのは完備化されるSであり、基底BのNoether性は不要。 -/
theorem exists_complete_flat_local_extension_with_residue
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S)
    (e : ResidueField S ≃+* K)
    (he : ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x)
    (a : K) (s : S) (hs : e (residue S s) = a) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ eC : ResidueField C ≃+* K,
        (∀ x, eC (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x) ∧
        ∃ c : C, eC (residue C c) = a := by
  let C := AdicCompletion (maximalIdeal S) S
  let : IsScalarTower B S C := inferInstance
  let : IsNoetherianRing C := isNoetherianRing_adicCompletion S (maximalIdeal S)
  let : IsLocalHom (algebraMap B C) := by
    rw [IsScalarTower.algebraMap_eq B S C]
    infer_instance
  let : Module.Flat B C := Module.Flat.trans B S C
  have hcmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C := by
    rw [IsScalarTower.algebraMap_eq B S C, ← Ideal.map_map, hmax]
    exact AdicCompletion.maximalIdeal_eq_map.symm
  let eC : ResidueField C ≃+* K :=
    adicCompletionTargetResidueEquiv (maximalIdeal S).fg_of_isNoetherianRing e
  have hev (t : S) : eC (residue C (algebraMap S C t)) = e (residue S t) :=
    adicCompletionTargetResidueEquiv_apply (maximalIdeal S).fg_of_isNoetherianRing e t
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcmax, eC, ?_, algebraMap S C s, ?_⟩
  · exact adicCompletionTargetResidueEquiv_base_map
      (maximalIdeal S).fg_of_isNoetherianRing e he
  · rw [hev]
    exact hs

end Completion

section Algebraic

open IsLocalRing Polynomial

/-- 剰余体上のモニック多項式は、同じ次数のモニック多項式へ持ち上がる。 -/
theorem exists_monic_residue_lift {B : Type*} [CommRing B] [IsLocalRing B]
    (f : Polynomial (ResidueField B)) (hf : f.Monic) :
    ∃ F : Polynomial B, F.map (residue B) = f ∧ F.degree = f.degree ∧ F.Monic :=
  Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := B)) f) hf

section ClosedFibre
variable {B K : Type*} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable (pb : PowerBasis (ResidueField B) K) (F : Polynomial B)
variable (hF : F.map (residue B) = minpoly (ResidueField B) pb.gen)

/-- 持ち上げた最小多項式の閉ファイバーを指定体へ同定する基底環上の代数同型。 -/
noncomputable def liftedMinpolyClosedFibreEquiv :
    (AdjoinRoot F ⧸ (maximalIdeal B).map (algebraMap B (AdjoinRoot F))) ≃ₐ[B] K := by
  have h₁ : aeval (AdjoinRoot.root (F.map (residue B)))
      (minpoly (ResidueField B) pb.gen) = 0 := by
    rw [← hF, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h₂ : aeval pb.gen (F.map (residue B)) = 0 := by
    rw [hF]
    exact minpoly.aeval _ _
  exact (adjoinRoot_closedFibreEquiv F).trans
    ((AdjoinRoot.equiv' (F.map (residue B)) pb h₁ h₂).restrictScalars B)

/-- 閉ファイバーの同型は、多項式の根を指定体の冪基底生成元へ送る。 -/
@[simp] theorem liftedMinpolyClosedFibreEquiv_root :
    liftedMinpolyClosedFibreEquiv pb F hF
      (Ideal.Quotient.mk _ (AdjoinRoot.root F)) = pb.gen := by
  simp only [liftedMinpolyClosedFibreEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, adjoinRoot_closedFibreEquiv_root]
  rw [← AlgEquiv.coe_toAlgHom, AdjoinRoot.equiv'_toAlgHom]
  -- aevalとeval₂の定義上の同一視を、Mathlibの根の計算への適用だけで展開する。
  with_unfolding_all exact AdjoinRoot.liftAlgHom_root _ _ _ _

end ClosedFibre

/-- 冪基底を持つ指定剰余体を、有限自由な平坦局所拡大として持ち上げる。
実際の環は持ち上げたモニック多項式の商。剰余体同型は基底の剰余体上で両立し、
多項式の根も指定された生成元へ送る。完備性・Noether性・分離性は要求しない。 -/
theorem exists_finite_free_local_extension_of_powerBasis
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (pb : PowerBasis (ResidueField B) K) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Free B S ∧ Module.Finite B S ∧ Module.Flat B S ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ a : S, e (residue S a) = pb.gen := by
  classical
  let : Algebra B K := ((algebraMap (ResidueField B) K).comp (residue B)).toAlgebra
  let : IsScalarTower B (ResidueField B) K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨F, hFmap, hFdegree, hFmonic⟩ :=
    exists_monic_residue_lift (minpoly (ResidueField B) pb.gen) (minpoly.monic pb.isIntegral_gen)
  let S := AdjoinRoot F
  let eq : (S ⧸ (maximalIdeal B).map (algebraMap B S)) ≃ₐ[B] K :=
    liftedMinpolyClosedFibreEquiv pb F hFmap
  have hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S)) :=
    MulEquiv.isField (Field.toIsField K) eq.toRingEquiv.toMulEquiv
  let : Algebra.IsIntegral B S := AdjoinRoot.isIntegral_of_monic hFmonic
  let : IsLocalRing S := isLocalRing_of_integral_of_field_closedFibre B S hfield
  have hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S :=
    maximalIdeal_map_eq_of_field_closedFibre B S hfield
  let : IsLocalHom (algebraMap B S) := AdjoinRoot.isLocalHom_of_monic_of_degree_pos hFmonic
    (by rw [hFdegree]; exact minpoly.degree_pos pb.isIntegral_gen)
  let e : ResidueField S ≃+* K := (Ideal.quotEquivOfEq hmax.symm).trans eq.toRingEquiv
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    hFmonic.free_adjoinRoot, hFmonic.finite_adjoinRoot,
    (letI := hFmonic.free_adjoinRoot; inferInstance),
    hmax, e, ?_, AdjoinRoot.root F, ?_⟩
  · intro x
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
    rw [ResidueField.map_residue]
    change eq ((Ideal.quotEquivOfEq hmax.symm)
      (Ideal.Quotient.mk (maximalIdeal S) (algebraMap B S b))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact eq.commutes b
  · change eq ((Ideal.quotEquivOfEq hmax.symm)
      (Ideal.Quotient.mk (maximalIdeal S) (AdjoinRoot.root F))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact liftedMinpolyClosedFibreEquiv_root pb F hFmap

/-- 代数的な一元で生成された指定体について、同じ生成元に両立する局所拡大を構成する。
冪基底は一元による生成と整性から実際に作るため、分離的な原始元定理は不要。 -/
theorem exists_finite_free_local_extension_of_integral_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : IsIntegral (ResidueField B) a)
    (hgen : Algebra.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Free B S ∧ Module.Finite B S ∧ Module.Flat B S ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  simpa only [PowerBasis.ofAdjoinEqTop_gen] using
    exists_finite_free_local_extension_of_powerBasis B K (PowerBasis.ofAdjoinEqTop ha hgen)

end Algebraic

section Transcendental

open IsLocalRing Polynomial

/-- 剰余体へ係数を還元してから、指定された元で評価する。 -/
noncomputable def residuePolynomialEval
    (B : Type*) [CommRing B] [IsLocalRing B]
    {K : Type*} [Field K] [Algebra (ResidueField B) K] (a : K) : B[X] →+* K :=
  (aeval a).toRingHom.comp (Polynomial.mapRingHom (residue B))

/-- 超越的な評価の核は、基底の極大イデアルの多項式環への拡張である。 -/
theorem residuePolynomialEval_ker
    (B : Type*) [CommRing B] [IsLocalRing B]
    {K : Type*} [Field K] [Algebra (ResidueField B) K] (a : K)
    (ha : Transcendental (ResidueField B) a) :
    RingHom.ker (residuePolynomialEval B a) = (maximalIdeal B).map Polynomial.C := by
  rw [residuePolynomialEval, RingHom.ker_comp_of_injective _
    (transcendental_iff_injective.mp ha), Polynomial.ker_mapRingHom, ker_residue]

/-- 超越的な一元で生成された指定体を、平坦局所拡大の剰余体として実現する。
Noether性は要求しない。基底がNoetherなら、構成した局所化もNoetherである。 -/
theorem exists_flat_local_extension_of_transcendental_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : Transcendental (ResidueField B) a)
    (hgen : IntermediateField.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (IsNoetherianRing B → IsNoetherianRing S) ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  classical
  let f := residuePolynomialEval B a
  let P := RingHom.ker f
  let : P.IsPrime := RingHom.ker_isPrime f
  let S := Localization.AtPrime P
  have hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S := by
    rw [IsScalarTower.algebraMap_eq B B[X] S, ← Ideal.map_map,
      Polynomial.algebraMap_eq, ← residuePolynomialEval_ker B a ha]
    exact Localization.AtPrime.map_eq_maximalIdeal
  let : IsLocalHom (algebraMap B S) := ⟨fun b hb ↦ by
    by_contra hn
    have hm : b ∈ maximalIdeal B := hn
    have hm' := Ideal.mem_map_of_mem (algebraMap B S) hm
    rw [hmax] at hm'
    exact hm' hb⟩
  have hu (q : P.primeCompl) : IsUnit (f q) :=
    isUnit_iff_ne_zero.mpr q.property
  let g : S →+* K := IsLocalization.lift hu
  have hg : Function.Surjective g := by
    apply (IsLocalization.lift_surjective_iff hu).mpr
    intro z
    by_cases hz : z = 0
    · subst z
      exact ⟨(0, 1), by simp⟩
    obtain ⟨p, q, hzpq⟩ := (IntermediateField.mem_adjoin_simple_iff (ResidueField B) z).mp
      (hgen.symm ▸ IntermediateField.mem_top)
    obtain ⟨pB, hpB⟩ := Polynomial.map_surjective (residue B)
      (residue_surjective (R := B)) p
    obtain ⟨qB, hqB⟩ := Polynomial.map_surjective (residue B)
      (residue_surjective (R := B)) q
    have hq : aeval a q ≠ 0 := by
      intro hq
      apply hz
      rw [hzpq, hq, div_zero]
    have hqB' : qB ∈ P.primeCompl := by
      change f qB ≠ 0
      simpa [f, residuePolynomialEval, hqB] using hq
    refine ⟨(pB, ⟨qB, hqB'⟩), ?_⟩
    change z * f qB = f pB
    simp only [f, residuePolynomialEval, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      hpB, hqB]
    change z * aeval a q = aeval a p
    rw [hzpq, div_mul_cancel₀ _ hq]
  have hgker : RingHom.ker g = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg)
  let e : ResidueField S ≃+* K := (Ideal.quotEquivOfEq hgker.symm).trans
    (g.quotientKerEquivOfSurjective hg)
  have hev (s : S) : e (residue S s) = g s := by
    change g.quotientKerEquivOfSurjective hg
      ((Ideal.quotEquivOfEq hgker.symm) (Ideal.Quotient.mk _ s)) = _
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, hmax, e, ?_, algebraMap B[X] S X, ?_⟩
  · intro h
    let : IsNoetherianRing B := h
    infer_instance
  · intro x
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
    rw [ResidueField.map_residue, hev]
    change g (algebraMap B[X] S (C b)) = _
    rw [IsLocalization.lift_eq]
    simp [f, residuePolynomialEval]
  · rw [hev, IsLocalization.lift_eq]
    simp [f, residuePolynomialEval]

end Transcendental

section SimpleExtension

open IsLocalRing

/-- 任意の単生成体拡大を剰余体として持つ平坦局所拡大を構成する。
代数的な場合はR1、超越的な場合はR2を適用する。 -/
theorem exists_flat_local_extension_of_simple_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (hgen : IntermediateField.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (IsNoetherianRing B → IsNoetherianRing S) ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  classical
  by_cases ha : IsAlgebraic (ResidueField B) a
  · let pb := PowerBasis.ofAdjoinSimpleEqTop ha.isIntegral hgen
    obtain ⟨S, sRing, sLocal, sAlg, sHom, sFree, sFinite, sFlat, hmax, e, he, s, hs⟩ :=
      exists_finite_free_local_extension_of_powerBasis B K pb
    refine ⟨S, sRing, sLocal, sAlg, sHom, sFlat, ?_, hmax, e, he, s, ?_⟩
    · intro h
      let : IsNoetherianRing B := h
      exact IsNoetherianRing.of_finite B S
    · simpa only [pb, PowerBasis.ofAdjoinSimpleEqTop_gen] using hs
  · exact exists_flat_local_extension_of_transcendental_generator B K a ha hgen

/-- 係数体の同型と両立する代数構造では、体生成の条件を移送できる。 -/
theorem adjoin_eq_top_of_scalar_equiv
    {F L K : Type*} [Field F] [Field L] [Field K] [Algebra F K] [Algebra L K]
    (e : F ≃+* L) (he : ∀ x, algebraMap F K x = algebraMap L K (e x))
    (s : Set K) (hs : IntermediateField.adjoin L s = ⊤) :
    IntermediateField.adjoin F s = ⊤ := by
  have hr : Set.range (algebraMap F K) = Set.range (algebraMap L K) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, (he y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by rw [he, e.apply_symm_apply]⟩
  have h : (IntermediateField.adjoin F s).toSubfield =
      (IntermediateField.adjoin L s).toSubfield := by
    simp only [IntermediateField.adjoin_toSubfield, hr]
  apply top_unique
  intro x _
  change x ∈ (IntermediateField.adjoin F s).toSubfield
  rw [h, hs]
  trivial

/-- 単生成中間体そのものは、その標準生成元で生成される。 -/
theorem adjoin_simple_gen_eq_top
    (F K : Type*) [Field F] [Field K] [Algebra F K] (a : K) :
    IntermediateField.adjoin F {IntermediateField.AdjoinSimple.gen F a} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin F {a}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
  rw [Set.image_singleton]
  rfl

end SimpleExtension

section Successor

open IsLocalRing

/-- 構成済みの局所拡大の剰余体へ一元を加える後続段。
旧段からの実際の係数写像、その平坦性・局所性、基底からの合成、剰余体の両立を供給する。 -/
theorem exists_residueField_successor
    (B S K : Type u) [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S]
    [IsLocalHom (algebraMap B S)] [Module.Flat B S]
    [Field K] [Algebra (ResidueField B) K]
    (L : IntermediateField (ResidueField B) K)
    (eS : ResidueField S ≃+* L)
    (heS : ∀ y, eS (ResidueField.map (algebraMap B S) y) = algebraMap (ResidueField B) L y)
    (hsmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S) (a : K) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsLocalRing T)
      (_ : Algebra S T) (_ : Algebra B T) (_ : IsScalarTower B S T)
      (_ : IsLocalHom (algebraMap S T)) (_ : IsLocalHom (algebraMap B T)),
      Module.Flat S T ∧ Module.Flat B T ∧ (IsNoetherianRing S → IsNoetherianRing T) ∧
      (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ∧
      (maximalIdeal B).map (algebraMap B T) = maximalIdeal T ∧
      ∃ eT : ResidueField T ≃+* IntermediateField.adjoin L {a},
        (∀ y, eT (ResidueField.map (algebraMap B T) y) =
          algebraMap (ResidueField B) (IntermediateField.adjoin L {a}) y) ∧
        (∀ y, eT (ResidueField.map (algebraMap S T) y) =
          algebraMap L (IntermediateField.adjoin L {a}) (eS y)) ∧
        ∃ t : T, eT (residue T t) = IntermediateField.AdjoinSimple.gen L a := by
  let E := IntermediateField.adjoin L {a}
  let : Algebra (ResidueField S) E := ((algebraMap L E).comp eS.toRingHom).toAlgebra
  have hgen : IntermediateField.adjoin (ResidueField S)
      {IntermediateField.AdjoinSimple.gen L a} = ⊤ :=
    adjoin_eq_top_of_scalar_equiv eS (fun _ ↦ rfl) _ (adjoin_simple_gen_eq_top L K a)
  obtain ⟨T, tRing, tLocal, tAlg, tHom, tFlat, tNoeth, htmax, eT, heT, t, ht⟩ :=
    exists_flat_local_extension_of_simple_generator S E
      (IntermediateField.AdjoinSimple.gen L a) hgen
  let : Algebra B T := ((algebraMap S T).comp (algebraMap B S)).toAlgebra
  let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : IsLocalHom (algebraMap B T) := by
    rw [IsScalarTower.algebraMap_eq B S T]
    infer_instance
  let : Module.Flat B T := Module.Flat.trans B S T
  have hmax : (maximalIdeal B).map (algebraMap B T) = maximalIdeal T := by
    rw [IsScalarTower.algebraMap_eq B S T, ← Ideal.map_map, hsmax]
    exact htmax
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, tFlat, inferInstance, tNoeth, htmax, hmax, eT, ?_, heT, t, ht⟩
  intro y
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) y
  rw [ResidueField.map_residue]
  change eT (residue T (algebraMap S T (algebraMap B S b))) = _
  rw [← ResidueField.map_residue, heT]
  change algebraMap L E (eS (residue S (algebraMap B S b))) = _
  rw [← ResidueField.map_residue, heS]
  rfl

end Successor

section Finite

open IsLocalRing

/-- 有限生成中間体を、Noether平坦局所拡大の指定剰余体として構成する。
Mathlibの単生成拡大による帰納法を使い、各段では完備化しない。 -/
theorem exists_noetherian_flat_local_extension_of_fg_intermediateField
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (L : IntermediateField (ResidueField B) K) (hL : L.FG) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* L,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) L x := by
  classical
  refine IntermediateField.induction_on_adjoin_fg (motive := fun L ↦
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* L,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) L x)
    ?_ ?_ L hL
  · let e := (IntermediateField.botEquiv (ResidueField B) K).symm
    refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, e.toRingEquiv, ?_⟩
    · simp
    · intro x
      obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
      rw [ResidueField.map_residue]
      exact e.commutes (residue B b)
  · intro L x ih
    obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hsmax, eS, heS⟩ := ih
    obtain ⟨T, tRing, tLocal, tAlgS, tAlgB, tTower, tHomS, tHomB,
      tFlatS, tFlatB, tNoeth, htmax, hmax, eT, heT, heStep, t, ht⟩ :=
      exists_residueField_successor B S K L eS heS hsmax x
    let : IsNoetherianRing T := tNoeth inferInstance
    exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, tFlatB, hmax, eT, heT⟩

/-- 指定された有限生成体拡大に対応するNoether平坦局所拡大。 -/
theorem exists_noetherian_flat_local_extension_of_fg
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (hK : (⊤ : IntermediateField (ResidueField B) K).FG) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsNoetherianRing S)
      (_ : Algebra B S) (_ : IsLocalHom (algebraMap B S)),
      Module.Flat B S ∧ (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_noetherian_flat_local_extension_of_fg_intermediateField B K ⊤ hK
  let q := IntermediateField.topEquiv (F := ResidueField B) (E := K)
  refine ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax,
    e.trans q.toRingEquiv, ?_⟩
  intro x
  change q (e (ResidueField.map (algebraMap B S) x)) = _
  rw [he]
  exact q.commutes x

/-- 外部引用1の有限生成体拡大版。最後に一度だけ完備化する。
一般の体拡大の引用や、R3/R4の有向極限の証明には依存しない。 -/
theorem exists_complete_flat_local_extension_of_fg
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (hK : (⊤ : IntermediateField (ResidueField B) K).FG) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  obtain ⟨S, sRing, sLocal, sNoeth, sAlg, sHom, sFlat, hmax, e, he⟩ :=
    exists_noetherian_flat_local_extension_of_fg B K hK
  obtain ⟨C, cRing, cLocal, cNoeth, cComplete, cAlg, cHom, cFlat, hcmax, eC, heC, c, hc⟩ :=
    exists_complete_flat_local_extension_with_residue B S K hmax e he 0 0 (map_zero e)
  exact ⟨C, cRing, cLocal, cNoeth, cComplete, cAlg, cHom, cFlat, hcmax, eC, heC⟩

/-- 有限個の指定体生成元から、完備Noether平坦局所拡大を構成する。
空集合も許し、その場合は帰納法の基底から完備化する。 -/
theorem exists_complete_flat_local_extension_of_finset
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (s : Finset K) (hs : IntermediateField.adjoin (ResidueField B) (s : Set K) = ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  apply exists_complete_flat_local_extension_of_fg B K
  rw [← hs]
  exact IntermediateField.fg_adjoin_finset s

/-- Mathlibの有限生成体拡大の型クラスから適用する入口。 -/
theorem exists_complete_flat_local_extension_of_essFiniteType
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    [Algebra.EssFiniteType (ResidueField B) K] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  exact exists_complete_flat_local_extension_of_fg B K
    (IntermediateField.fg_top_iff.mpr inferInstance)

end Finite

end SerrePositivity
