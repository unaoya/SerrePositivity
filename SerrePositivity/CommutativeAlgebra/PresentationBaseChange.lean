module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 表示された加群の係数拡大と代数の積写像の像

## 概要

`R` 代数 `S` と、有限個の関係式 `r : κ → (ι → R)` で表示された `R` 加群 `R^ι / span r` について、
係数拡大は関係式の像で表示される：

  `S ⊗_R (R^ι / span_R (r)) ≃ S^ι / span_S (ρ ∘ r)`（`S` 線形、`ρ : R^ι → S^ι` は各成分に `algebraMap`）。

テンソル積の右完全性の具体形で、`Mathlib` の `TensorProduct.tensorQuotientEquiv` は `R` 線形にしか
述べられていないので、`S` 線形な同型を直接作る。順方向は `R^ι/span r → S^ι/span (ρ r)` の
`liftBaseChange`、逆方向は `e_i ↦ 1 ⊗ [e_i]` で、どちらも生成元で確かめる。

## 使われ方

塔の段への降下（`Paper/Section2/TowerDescent.lean`）：`Λ` 加群の有限表示を段 `A_n` に降ろしたとき、
`Λ ⊗_{A_n} (A_n^l / span d) ≃ Λ^l / span (ρ d)` で元の加群に戻ることを示す。
-/

@[expose] public section

open TensorProduct

namespace SerrePositivity

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (ι : Type*)

/-- 係数拡大 `R^ι → S^ι`（各成分に `algebraMap`）。`R` 線形。 -/
def piAlgebraMap : (ι → R) →ₗ[R] (ι → S) := LinearMap.compLeft (Algebra.linearMap R S) ι

variable {R S ι}

lemma piAlgebraMap_apply (v : ι → R) (i : ι) : piAlgebraMap R S ι v i = algebraMap R S (v i) := rfl

lemma piAlgebraMap_single [DecidableEq ι] (i : ι) (a : R) :
    piAlgebraMap R S ι (Pi.single i a) = Pi.single i (algebraMap R S a) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [piAlgebraMap_apply]
  · simp [piAlgebraMap_apply, hj]

variable [Fintype ι] [DecidableEq ι] {κ : Type*} (S) (r : κ → (ι → R))

/-- `R^ι / span r → S^ι / span (ρ r)`（`R` 線形）。 -/
noncomputable def quotPiAlgebraMap :
    ((ι → R) ⧸ Submodule.span R (Set.range r)) →ₗ[R]
      ((ι → S) ⧸ Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))) :=
  (Submodule.span R (Set.range r)).liftQ
    (((Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))).mkQ.restrictScalars R).comp
      (piAlgebraMap R S ι)) (by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨j, rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma quotPiAlgebraMap_mk (v : ι → R) :
    quotPiAlgebraMap S r (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (piAlgebraMap R S ι v) :=
  rfl

/-- 順方向 `S ⊗_R (R^ι / span r) → S^ι / span (ρ r)`。 -/
noncomputable def baseChangeQuotToPi :
    S ⊗[R] ((ι → R) ⧸ Submodule.span R (Set.range r)) →ₗ[S]
      ((ι → S) ⧸ Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))) :=
  (quotPiAlgebraMap S r).liftBaseChange S

/-- 逆方向の原型 `S^ι → S ⊗_R (R^ι / span r)`、`e_i ↦ 1 ⊗ [e_i]`。 -/
noncomputable def piToBaseChangeQuot :
    (ι → S) →ₗ[S] S ⊗[R] ((ι → R) ⧸ Submodule.span R (Set.range r)) :=
  Fintype.linearCombination S fun i ↦
    (1 : S) ⊗ₜ[R] (Submodule.Quotient.mk (Pi.single i 1) : (ι → R) ⧸ Submodule.span R (Set.range r))

/-- `R^ι` の元 `v` について `piToBaseChangeQuot (ρ v) = 1 ⊗ [v]`。 -/
lemma piToBaseChangeQuot_piAlgebraMap (v : ι → R) :
    piToBaseChangeQuot S r (piAlgebraMap R S ι v) = (1 : S) ⊗ₜ[R] Submodule.Quotient.mk v := by
  have : ((piToBaseChangeQuot S r).restrictScalars R).comp (piAlgebraMap R S ι) =
      (TensorProduct.mk R S _ 1).comp (Submodule.span R (Set.range r)).mkQ := by
    refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
    simp [piToBaseChangeQuot, piAlgebraMap_single]
  exact LinearMap.congr_fun this v

/-- 逆方向 `S^ι / span (ρ r) → S ⊗_R (R^ι / span r)`。 -/
noncomputable def baseChangeQuotOfPi :
    ((ι → S) ⧸ Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))) →ₗ[S]
      S ⊗[R] ((ι → R) ⧸ Submodule.span R (Set.range r)) :=
  (Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))).liftQ (piToBaseChangeQuot S r) (by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Function.comp_apply, piToBaseChangeQuot_piAlgebraMap,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (Set.mem_range_self j)),
      tmul_zero])

/-- **表示された加群の係数拡大**：`S ⊗_R (R^ι / span r) ≃ S^ι / span (ρ ∘ r)`（`S` 線形）。 -/
noncomputable def baseChangeQuotEquiv :
    S ⊗[R] ((ι → R) ⧸ Submodule.span R (Set.range r)) ≃ₗ[S]
      ((ι → S) ⧸ Submodule.span S (Set.range (piAlgebraMap R S ι ∘ r))) :=
  LinearEquiv.ofLinearMap (baseChangeQuotToPi S r) (baseChangeQuotOfPi S r)
    (by
      refine Submodule.linearMap_qext _ ?_
      refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
      simp [baseChangeQuotToPi, baseChangeQuotOfPi, piToBaseChangeQuot, quotPiAlgebraMap_mk,
        piAlgebraMap_single])
    (by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.inductionOn with
      | tmul s v =>
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
        simp only [LinearMap.comp_apply, baseChangeQuotToPi, LinearMap.liftBaseChange_tmul,
          quotPiAlgebraMap_mk, baseChangeQuotOfPi, map_smul, Submodule.liftQ_apply,
          piToBaseChangeQuot_piAlgebraMap, LinearMap.id_apply, smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy])

lemma baseChangeQuotEquiv_tmul_mk (s : S) (v : ι → R) :
    baseChangeQuotEquiv S r (s ⊗ₜ[R] Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (s • piAlgebraMap R S ι v) := by
  change baseChangeQuotToPi S r (s ⊗ₜ[R] Submodule.Quotient.mk v) = _
  rw [baseChangeQuotToPi, LinearMap.liftBaseChange_tmul, quotPiAlgebraMap_mk,
    Submodule.Quotient.mk_smul]

lemma baseChangeQuotEquiv_symm_mk (w : ι → S) :
    (baseChangeQuotEquiv S r).symm (Submodule.Quotient.mk w) = piToBaseChangeQuot S r w :=
  rfl


/-- 係数拡大から環への積写像の像は、係数環上で右因子の像が生成する部分代数である。 -/
theorem tensorProduct_range_eq_adjoin
    (S R T C : Type u) [CommRing S] [CommRing R] [CommRing T] [CommRing C]
    [Algebra S R] [Algebra S T] [Algebra S C] [Algebra R C] [IsScalarTower S R C]
    (g : T →ₐ[S] C) :
    (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId R C) g).range =
      Algebra.adjoin R (Set.range g) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul r t =>
        change algebraMap R C r * g t ∈ _
        exact (Algebra.adjoin R (Set.range g)).mul_mem
          (Subalgebra.algebraMap_mem _ r) (Algebra.subset_adjoin (Set.mem_range_self t))
    | add x y hx hy =>
        rw [map_add]
        exact (Algebra.adjoin R (Set.range g)).add_mem hx hy
  · apply Algebra.adjoin_le
    rintro x ⟨t, rfl⟩
    refine ⟨1 ⊗ₜ[S] t, ?_⟩
    change algebraMap R C 1 * g t = g t
    rw [map_one, one_mul]


/-- 係数拡大の環同型は、右因子のイデアルで割った商にも降りる。
Mathlib のテンソル積と商の交換を、与えられた代数同型と合成する。 -/
noncomputable def baseChangeIdealQuotientEquiv
    (S R T B : Type u) [CommRing S] [CommRing R] [CommRing T] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R B]
    (e : R ⊗[S] T ≃ₐ[R] B) (I : Ideal T) :
    R ⊗[S] (T ⧸ I) ≃ₐ[R]
      B ⧸ I.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := S) R T R I).trans
    (Ideal.quotientEquivAlg _ _ e (I.map_map _ _).symm)

end SerrePositivity
