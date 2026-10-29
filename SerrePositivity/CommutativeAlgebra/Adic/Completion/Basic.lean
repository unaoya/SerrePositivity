module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import SerrePositivity.CommutativeAlgebra.Adic.Finite
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Over

/-! # イデアル進完備化の基本

概要：有限生成イデアル `I` に沿う完備化 `M̂ = AdicCompletion I M` について
- 分離な加群への `M̂` からの線形写像は、`M` の像の上で決まる。
- `M̂ / I^n M̂ ≅ M / I^n M`。最初の商が有限で `R` が前完備なら `M̂` は有限。
- 環の完備化の `n` 段評価の核は `I^n R̂`。`I^n ≤ H` なる `H` について `R̂ / H R̂ ≅ R / H`（`H = I^n` が冪商の同型）。
  元の環の元は任意の冪商で `R̂` の元を代表する。
- 底環の冪商の上での同型（`R → S` で `I S` に沿う完備化）。
方針：Mathlib の `AdicCompletion.pow_smul_top_eq_ker_eval`・`eval_surjective`・`surjective_evalₐ` から。
規約：イデアルは有限生成を仮定する。
使われ方：完備化の完全性・テンソル・代数構造（`Adic/Completion/*`）、Bhatt–Scholze 側。
Mathlib への提出候補（`n` 段の核は Mathlib の `ker_evalOneₐ_eq_map` の一般化）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicCompletionExt

/-- 有限生成イデアルの完備化から分離加群への線形写像は、元の加群の像で決まる。 -/
theorem adicCompletion_linearMap_ext_of_of {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (hI : I.FG) [IsHausdorff I N]
    (f g : AdicCompletion I M →ₗ[R] N)
    (h : f.comp (AdicCompletion.of I M) = g.comp (AdicCompletion.of I M)) : f = g := by
  apply LinearMap.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
      AdicCompletion.eval_of]
    exact sub_eq_zero.mpr ha.symm
  have hm (l : AdicCompletion I M →ₗ[R] N) :
      l x ≡ l (AdicCompletion.of I M a) [SMOD I ^ n • (⊤ : Submodule R N)] := by
    apply SModEq.sub_mem.mpr
    rw [← map_sub]
    have hl : l (x - AdicCompletion.of I M a) ∈
        (I ^ n • (⊤ : Submodule R (AdicCompletion I M))).map l := ⟨_, hx, rfl⟩
    rw [Submodule.map_smul''] at hl
    exact Submodule.smul_mono le_rfl le_top hl
  have he : f (AdicCompletion.of I M a) = g (AdicCompletion.of I M a) := LinearMap.congr_fun h a
  exact (hm f).trans (he ▸ (hm g).symm)

end AdicCompletionExt

section AdicCompletionFinite

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限生成イデアルの完備化の冪商は、元の加群の同じ冪商と同型。 -/
def adicCompletionQuotientEquiv (I : Ideal R) (hI : I.FG) (n : ℕ) :
    (AdicCompletion I M ⧸ I ^ n • (⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      M ⧸ I ^ n • (⊤ : Submodule R M) :=
  (Submodule.quotEquivOfEq _ _ (AdicCompletion.pow_smul_top_eq_ker_eval hI)).trans
    ((AdicCompletion.eval I M n).quotKerEquivOfSurjective (AdicCompletion.eval_surjective I M n))

@[simp] theorem adicCompletionQuotientEquiv_mk (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I M) :
    adicCompletionQuotientEquiv I hI n (Submodule.Quotient.mk x) =
      AdicCompletion.eval I M n x := by
  simp [adicCompletionQuotientEquiv]

/-- 前完備な環上では、最初のイデアル商が有限なら完備化も有限。 -/
theorem moduleFinite_adicCompletion_of_finite_quotient (I : Ideal R) (hI : I.FG)
    [IsPrecomplete I R] [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Finite R (AdicCompletion I M) := by
  let : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  let E : (AdicCompletion I M ⧸ I • (⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      M ⧸ I • (⊤ : Submodule R M) := by
    have E := adicCompletionQuotientEquiv (M := M) I hI 1
    rw [pow_one] at E
    exact E
  let : Module.Finite R
      (AdicCompletion I M ⧸ I • (⊤ : Submodule R (AdicCompletion I M))) :=
    Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := AdicCompletion I M) I
  exact Module.Finite.of_surjective f hf

end AdicCompletionFinite

section AdicCompletionQuotient

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
include hI

/-- 有限生成イデアルに沿う完備化のn段評価の核。 -/
theorem adicCompletion_ker_eval_eq_map (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (AdicCompletion.eval I R n).ker
  · change (Ideal.quotientEquivAlgOfEq R
      (show (I ^ n • ⊤ : Ideal R) = I ^ n from by ext; simp))
        (AdicCompletion.eval I R n x) = 0 ↔ AdicCompletion.eval I R n x = 0
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval hI]

/-- 完備化に拡張したイデアルのn乗が評価の核となる。 -/
theorem adicCompletion_ker_eval_eq_pow_map (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  rw [adicCompletion_ker_eval_eq_map I hI, Ideal.map_pow]

/-- 完備化の元は、任意の冪商で元の環からの像によって代表できる。 -/
theorem exists_adicCompletion_algebraMap_sub_mem (n : ℕ) (x : AdicCompletion I R) :
    ∃ r : R, algebraMap R (AdicCompletion I R) r - x ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  rw [← adicCompletion_ker_eval_eq_map I hI n]
  change AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r - x) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  exact sub_eq_zero.mpr hr

/-- 元環の元について、完備化後の拡大冪イデアルへの所属は元環での所属と同値。 -/
theorem adicCompletion_algebraMap_mem_map_pow_iff (n : ℕ) (r : R) :
    algebraMap R (AdicCompletion I R) r ∈
      (I ^ n).map (algebraMap R (AdicCompletion I R)) ↔ r ∈ I ^ n := by
  rw [← adicCompletion_ker_eval_eq_map I hI n]
  change AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = 0 ↔ _
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  simpa using (Ideal.Quotient.eq_zero_iff_mem (I := I ^ n) (a := r))

end AdicCompletionQuotient

section AdicCompletionOpenQuotient

variable {R : Type u} [CommRing R] (I H : Ideal R) (n : ℕ) (hn : I ^ n ≤ H)

/-- n段評価をHによる商へ送る標準代数写像。 -/
def adicCompletionOpenQuotientMap : AdicCompletion I R →ₐ[R] R ⧸ H :=
  (Ideal.Quotient.factorₐ R hn).comp (AdicCompletion.evalₐ I n)

@[simp] theorem adicCompletionOpenQuotientMap_algebraMap (r : R) :
    adicCompletionOpenQuotientMap I H n hn (algebraMap R (AdicCompletion I R) r) =
      Ideal.Quotient.mk H r := by
  simp [adicCompletionOpenQuotientMap, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of]

/-- 開イデアルによる商への評価は全射。 -/
theorem adicCompletionOpenQuotientMap_surjective :
    Function.Surjective (adicCompletionOpenQuotientMap I H n hn) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap R (AdicCompletion I R) r,
    adicCompletionOpenQuotientMap_algebraMap I H n hn r⟩

/-- 開イデアルによる商への評価の核は、そのイデアルの完備化への拡張。 -/
theorem adicCompletionOpenQuotientMap_ker (hI : I.FG) :
    RingHom.ker (adicCompletionOpenQuotientMap I H n hn).toRingHom =
      H.map (algebraMap R (AdicCompletion I R)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hrH : r ∈ H := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hzero : adicCompletionOpenQuotientMap I H n hn x = 0 := hx
      change (Ideal.Quotient.factorₐ R hn) (AdicCompletion.evalₐ I n x) = 0 at hzero
      rw [← hr] at hzero
      exact hzero
    have hd : x - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
      rw [← adicCompletion_ker_eval_eq_map I hI n]
      change AdicCompletion.evalₐ I n (x - algebraMap R (AdicCompletion I R) r) = 0
      rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
      exact sub_eq_zero.mpr hr.symm
    have hdH := Ideal.map_mono hn hd
    have hrmap := Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) hrH
    simpa using (H.map (algebraMap R (AdicCompletion I R))).add_mem hdH hrmap
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change adicCompletionOpenQuotientMap I H n hn (algebraMap R (AdicCompletion I R) r) = 0
    rw [adicCompletionOpenQuotientMap_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- 完備化してから開イデアルで割ることと、元の環で割ることはR代数として同型。 -/
def adicCompletionOpenQuotientEquiv (hI : I.FG) :
    (AdicCompletion I R ⧸ H.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ H :=
  (Ideal.quotientEquivAlgOfEq R (adicCompletionOpenQuotientMap_ker I H n hn hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (adicCompletionOpenQuotientMap_surjective I H n hn))

@[simp] theorem adicCompletionOpenQuotientEquiv_mk (hI : I.FG) (x : AdicCompletion I R) :
    adicCompletionOpenQuotientEquiv I H n hn hI (Ideal.Quotient.mk _ x) =
      adicCompletionOpenQuotientMap I H n hn x := by
  with_unfolding_all
    change (Ideal.quotientKerAlgEquivOfSurjective
        (adicCompletionOpenQuotientMap_surjective I H n hn))
      ((Ideal.quotientEquivAlgOfEq R (adicCompletionOpenQuotientMap_ker I H n hn hI).symm)
        (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk _ x

end AdicCompletionOpenQuotient

section PowQuotient

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- 完備化の冪商と元の環の冪商の係数を保つ同型。開いた商の同型の `H = I^n` の場合。 -/
noncomputable def adicCompletionPowQuotientEquiv (n : ℕ) :
    (AdicCompletion I R ⧸ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)) ≃ₐ[R]
      (R ⧸ (I ^ n)) :=
  (Ideal.quotientEquivAlgOfEq R (Ideal.map_pow _ I n).symm).trans
    (adicCompletionOpenQuotientEquiv I (I ^ n) n le_rfl hI)

/-- 同型は完備化の代表元をその `n` 段評価へ送る。 -/
@[simp] theorem adicCompletionPowQuotientEquiv_mk (n : ℕ) (x : AdicCompletion I R) :
    adicCompletionPowQuotientEquiv I hI n (Ideal.Quotient.mk _ x) =
      AdicCompletion.evalₐ I n x := by
  rw [adicCompletionPowQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    adicCompletionOpenQuotientEquiv_mk, adicCompletionOpenQuotientMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [AlgHom.comp_apply, ← hr]
  rfl

/-- 元の環からの係数写像との両立を、代表元で確認する。 -/
@[simp] theorem adicCompletionPowQuotientEquiv_algebraMap (n : ℕ) (x : R) :
    adicCompletionPowQuotientEquiv I hI n
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion I R) x)) =
        Ideal.Quotient.mk (I ^ n) x := by
  rw [adicCompletionPowQuotientEquiv_mk, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of]
  simp

end PowQuotient

section AdicCompletionBaseQuotient

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
variable (I : Ideal B) (hI : I.FG)

/-- 完備化の冪商を、基底の冪商上で元の環の冪商に同定する。 -/
noncomputable def adicCompletionBasePowQuotientEquiv (n : ℕ) :
    let J := I.map (algebraMap B S)
    let C := AdicCompletion J S
    (C ⧸ ((I ^ n).map (algebraMap B C))) ≃ₐ[B ⧸ (I ^ n)]
      (S ⧸ ((I ^ n).map (algebraMap B S))) := by
  let J := I.map (algebraMap B S)
  let C := AdicCompletion J S
  have hC : (J.map (algebraMap S C)) ^ n = (I ^ n).map (algebraMap B C) := by
    rw [Ideal.map_pow]
    have hmap : J.map (algebraMap S C) = I.map (algebraMap B C) := by
      change (I.map (algebraMap B S)).map (algebraMap S C) = _
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B S C]
    rw [hmap]
  have hS : J ^ n = (I ^ n).map (algebraMap B S) := by
    rw [Ideal.map_pow]
  let e : (C ⧸ ((I ^ n).map (algebraMap B C))) ≃ₐ[S]
      (S ⧸ ((I ^ n).map (algebraMap B S))) :=
    ((Ideal.quotientEquivAlgOfEq S hC.symm).trans
      (adicCompletionPowQuotientEquiv J (hI.map _) n)).trans
      (Ideal.quotientEquivAlgOfEq S hS)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e (Ideal.Quotient.mk _ (algebraMap B C b)) =
    Ideal.Quotient.mk _ (algebraMap B S b)
  rw [IsScalarTower.algebraMap_apply B S C]
  exact e.commutes (algebraMap B S b)

end AdicCompletionBaseQuotient

end SerrePositivity
