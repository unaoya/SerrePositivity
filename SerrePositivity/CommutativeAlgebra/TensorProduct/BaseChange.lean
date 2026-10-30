module

public import Mathlib.RingTheory.TensorProduct.Pi
public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 有限積・環同型・表示の基底変換

## 概要

有限積とテンソル積の交換、両立する基底の上のテンソル積の環同型、有限表示の基底変換を与える。

## 方針

テンソル積の写像は Mathlib の `Algebra.TensorProduct.mapRingHom` を使う。

## 規約

名前空間は SerrePositivity のまま。

## 使われ方

CLMST の階数の成分、PowTorsion の表示。
-/

@[expose] public noncomputable section

universe u v w z

section FiniteProductBaseChangePart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    {ι : Type w} [Finite ι] (B : ι → Type z) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- 左係数の有限直積を各底変換の直積へ移す、元の係数環上の代数同型。 -/
def finiteProductBaseChangeEquiv :
    ((i : ι) → B i) ⊗[R] S ≃ₐ[(i : ι) → B i] (i : ι) → B i ⊗[R] S := by
  classical
  letI := Fintype.ofFinite ι
  let e := (Algebra.TensorProduct.comm R ((i : ι) → B i) S).trans
    ((Algebra.TensorProduct.piRight R R S B).trans
      (AlgEquiv.piCongrRight (fun i => Algebra.TensorProduct.comm R S (B i))))
  refine AlgEquiv.ofRingEquiv (f := e.toRingEquiv) ?_
  intro b
  change e (b ⊗ₜ[R] (1 : S)) = fun i => b i ⊗ₜ[R] (1 : S)
  ext i
  simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]

/-- 全ての純 tensor の各成分をそのまま保つ。 -/
@[simp] theorem finiteProductBaseChangeEquiv_tmul
    (b : (i : ι) → B i) (s : S) (i : ι) :
    finiteProductBaseChangeEquiv R S B (b ⊗ₜ[R] s) i = b i ⊗ₜ[R] s := by
  classical
  simp only [finiteProductBaseChangeEquiv, AlgEquiv.ofRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]

/-- 元の S からの標準底変換写像は、各成分の同じ標準写像となる。 -/
@[simp] theorem finiteProductBaseChangeEquiv_unit (s : S) (i : ι) :
    finiteProductBaseChangeEquiv R S B ((1 : (i : ι) → B i) ⊗ₜ[R] s) i =
      (1 : B i) ⊗ₜ[R] s :=
  finiteProductBaseChangeEquiv_tmul R S B 1 s i

variable {C : ι → Type z} [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]

/-- 有限直積の元の各代数写像による底変換と、標準比較の各座標は可換である。 -/
theorem finiteProductBaseChangeEquiv_naturality
    (f : ∀ i, B i →ₐ[R] C i) (x : ((i : ι) → B i) ⊗[R] S) (i : ι) :
    finiteProductBaseChangeEquiv R S C
      (Algebra.TensorProduct.map
        (AlgHom.pi (fun j => (f j).comp (Pi.evalAlgHom R B j))) (AlgHom.id R S) x) i =
      Algebra.TensorProduct.map (f i) (AlgHom.id R S)
        (finiteProductBaseChangeEquiv R S B x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul b s =>
      simp only [Algebra.TensorProduct.map_tmul, finiteProductBaseChangeEquiv_tmul,
        AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end SerrePositivity

end FiniteProductBaseChangePart

section TensorRingEquivPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable {R R' A A' B B' : Type u}
    [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']

/-- Map both factors while retaining a compatible map of the base ring. -/
def tensorMapOfCompatibleBase (φ : R →+* R') (f : A →+* A') (g : B →+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (φ r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (φ r)) :
    A ⊗[R] B →+* A' ⊗[R'] B' :=
  Algebra.TensorProduct.mapRingHom φ f g (RingHom.ext hf) (RingHom.ext hg)

@[simp] lemma tensorMapOfCompatibleBase_tmul
    (φ : R →+* R') (f : A →+* A') (g : B →+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (φ r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (φ r)) (a : A) (b : B) :
    tensorMapOfCompatibleBase φ f g hf hg (a ⊗ₜ[R] b) = f a ⊗ₜ[R'] g b := by
  change (f a ⊗ₜ[R'] (1 : B')) * ((1 : A') ⊗ₜ[R'] g b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Compatible presentations identify the original ordinary tensor rings. -/
def tensorRingEquivOfCompatibleBase (e : R ≃+* R') (f : A ≃+* A') (g : B ≃+* B')
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R' A' (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R' B' (e r)) :
    A ⊗[R] B ≃+* A' ⊗[R'] B' := by
  have hf' : ∀ r, f.symm (algebraMap R' A' r) = algebraMap R A (e.symm r) := by
    intro r
    apply f.injective
    rw [f.apply_symm_apply, hf, e.apply_symm_apply]
  have hg' : ∀ r, g.symm (algebraMap R' B' r) = algebraMap R B (e.symm r) := by
    intro r
    apply g.injective
    rw [g.apply_symm_apply, hg, e.apply_symm_apply]
  let F := tensorMapOfCompatibleBase e.toRingHom f.toRingHom g.toRingHom hf hg
  let G := tensorMapOfCompatibleBase e.symm.toRingHom f.symm.toRingHom g.symm.toRingHom hf' hg'
  exact
    { F with
      invFun := G
      left_inv := fun x => by
        change G (F x) = x
        induction x using TensorProduct.inductionOn with
        | tmul a b => simp [F, G]
        | add x y hx hy => simp only [map_add, hx, hy]
      right_inv := fun x => by
        change F (G x) = x
        induction x using TensorProduct.inductionOn with
        | tmul a b => simp [F, G]
        | add x y hx hy => simp only [map_add, hx, hy] }

end SerrePositivity

end TensorRingEquivPart

section PresentationBaseChangePart

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

end PresentationBaseChangePart
