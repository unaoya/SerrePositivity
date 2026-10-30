module

public import SerrePositivity.CommutativeAlgebra.Adic.FlatTensorFiltration
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # 完備化とテンソル積・平坦性・係数制限

概要：
- 標準比較 `N ⊗ P̂ → (N ⊗ P)^`。`N` が有限なら全射、さらに `P` が平坦なら全単射。
- 平坦な `P` の完備化は（Noether 環上）平坦。平坦代数の冪商も平坦。
- 冪で零化される加群への係数拡大では、完備化は元の加群と同じ。
- 拡大したイデアル `I S` に沿う `S` 加群の完備化は、`R` 加群としての `I` 進完備化と同型。
方針：Mathlib の `AdicCompletion.ofTensorProduct` 系（`P = R` の場合）を、平坦な `P` へ一般化する。
規約：イデアルは有限生成、底環は必要な箇所で Noether。
使われ方：K 理論側（KST）、長さの代数（LengthAlgebra）。Mathlib への提出候補（`P = R` の一般化）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicCompletionTensor

open scoped TensorProduct

open LinearMap
variable {A : Type u} [CommRing A] (I : Ideal A)
    (N P : Type u) [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- 加群のテンソル積と完備化の自然な比較写像。 -/
def adicCompletionTensorComparison :
    N ⊗[A] AdicCompletion I P →ₗ[A] AdicCompletion I (N ⊗[A] P) :=
  TensorProduct.lift
    { toFun := fun n ↦ (AdicCompletion.map I (TensorProduct.mk A N P n)).restrictScalars A
      map_add' := by
        intro n m
        ext x
        simp
      map_smul' := by
        intro a n
        ext x
        simp }

@[simp] theorem adicCompletionTensorComparison_tmul (n : N) (x : AdicCompletion I P) :
    adicCompletionTensorComparison I N P (n ⊗ₜ[A] x) =
      AdicCompletion.map I (TensorProduct.mk A N P n) x := rfl

/-- 比較写像は元の加群からの標準写像と両立する。 -/
@[simp] theorem adicCompletionTensorComparison_tmul_of (n : N) (p : P) :
    adicCompletionTensorComparison I N P (n ⊗ₜ[A] AdicCompletion.of I P p) =
      AdicCompletion.of I (N ⊗[A] P) (n ⊗ₜ[A] p) := by
  simp [AdicCompletion.map_of]

/-- N 方向の線形写像についての自然性。 -/
theorem adicCompletionTensorComparison_natural
    {N' : Type u} [AddCommGroup N'] [Module A N'] (f : N →ₗ[A] N') :
    (AdicCompletion.map I (f.rTensor P)).restrictScalars A ∘ₗ
      adicCompletionTensorComparison I N P =
    adicCompletionTensorComparison I N' P ∘ₗ f.rTensor (AdicCompletion I P) := by
  apply TensorProduct.ext'
  intro n x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    adicCompletionTensorComparison_tmul, LinearMap.rTensor_tmul]
  rw [AdicCompletion.map_comp_apply]
  congr 1

/-- テンソル積の有限自由加群側を座標へ展開する同型。 -/
private def tensorPiEquiv (ι : Type) [Fintype ι] [DecidableEq ι]
    (Q : Type u) [AddCommGroup Q] [Module A Q] :
    (ι → A) ⊗[A] Q ≃ₗ[A] (ι → Q) :=
  (TensorProduct.comm A (ι → A) Q).trans (TensorProduct.piScalarRight A A Q ι)

private theorem tensorPiEquiv_tmul (ι : Type) [Fintype ι] [DecidableEq ι]
    (Q : Type u) [AddCommGroup Q] [Module A Q] (n : ι → A) (q : Q) :
    tensorPiEquiv (A := A) ι Q (n ⊗ₜ[A] q) = fun j ↦ n j • q := by
  simp [tensorPiEquiv]

/-- 有限自由加群との比較写像は同型。基底環の Noether 性と P の平坦性は不要。 -/
theorem adicCompletionTensorComparison_bijective_pi
    (ι : Type) [Finite ι] :
    Function.Bijective (adicCompletionTensorComparison I (ι → A) P) := by
  classical
  let := Fintype.ofFinite ι
  let e := tensorPiEquiv (A := A) ι P
  let out : AdicCompletion I ((ι → A) ⊗[A] P) ≃ₗ[A]
      (ι → AdicCompletion I P) :=
    ((AdicCompletion.congr I e).restrictScalars A).trans
      ((AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ P)).restrictScalars A)
  have heq : out.toLinearMap ∘ₗ adicCompletionTensorComparison I (ι → A) P =
      (tensorPiEquiv (A := A) ι (AdicCompletion I P)).toLinearMap := by
    apply TensorProduct.ext'
    intro n x
    apply funext
    intro j
    change ((AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ P))
      (AdicCompletion.congr I e
        (adicCompletionTensorComparison I (ι → A) P (n ⊗ₜ[A] x)))) j = _
    rw [AdicCompletion.piEquivOfFintype_apply]
    change AdicCompletion.map I (LinearMap.proj j)
      (AdicCompletion.map I e.toLinearMap
        (AdicCompletion.map I (TensorProduct.mk A (ι → A) P n) x)) = _
    rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
    have hc : (LinearMap.proj j ∘ₗ e.toLinearMap) ∘ₗ
        TensorProduct.mk A (ι → A) P n = n j • LinearMap.id := by
      ext p
      simp [e, tensorPiEquiv_tmul]
    rw [hc]
    simp [tensorPiEquiv_tmul]
  have hb : Function.Bijective
      (out.toLinearMap ∘ₗ adicCompletionTensorComparison I (ι → A) P) := by
    rw [heq]
    exact (tensorPiEquiv (A := A) ι (AdicCompletion I P)).bijective
  refine ⟨fun x y h ↦ hb.1 (congrArg out h), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (out y)
  exact ⟨x, out.injective hx⟩

/-- 有限加群の比較写像は全射。Noether 性や P の平坦性は不要。 -/
theorem adicCompletionTensorComparison_surjective [Module.Finite A N] :
    Function.Surjective (adicCompletionTensorComparison I N P) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A N
  have hs : Function.Surjective
      ((AdicCompletion.map I (q.rTensor P)).restrictScalars A ∘ₗ
        adicCompletionTensorComparison I (Fin n → A) P) :=
    (AdicCompletion.map_surjective I (LinearMap.rTensor_surjective P hq)).comp
      (adicCompletionTensorComparison_bijective_pi I P (Fin n)).2
  rw [adicCompletionTensorComparison_natural] at hs
  exact Function.Surjective.of_comp hs

/-- Noether 基底上の有限加群と、平坦加群の完備化との比較は単射。 -/
theorem adicCompletionTensorComparison_injective [IsNoetherianRing A]
    [Module.Finite A N] [Module.Flat A P] :
    Function.Injective (adicCompletionTensorComparison I N P) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A N
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective (AdicCompletion I P) hq x
  have hzero : AdicCompletion.map I (q.rTensor P)
      (adicCompletionTensorComparison I (Fin n → A) P y) = 0 := by
    have hn := congrArg (fun f ↦ f y) (adicCompletionTensorComparison_natural I
      (Fin n → A) P q)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hn
    rw [hy] at hn
    exact hn.trans hx
  have hex := adicCompletion_rTensor_exact_of_finite I q.ker.subtype q
    (Submodule.injective_subtype _) q.exact_subtype_ker_map hq (P := P)
  obtain ⟨z, hz⟩ := (hex (adicCompletionTensorComparison I (Fin n → A) P y)).mp hzero
  obtain ⟨w, hw⟩ := adicCompletionTensorComparison_surjective I q.ker P z
  have heq : (q.ker.subtype.rTensor (AdicCompletion I P)) w = y := by
    apply (adicCompletionTensorComparison_bijective_pi I P (Fin n)).1
    have hn := congrArg (fun f ↦ f w) (adicCompletionTensorComparison_natural I q.ker P
      q.ker.subtype)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hn
    rw [hw] at hn
    exact hn.symm.trans hz
  have hright := rTensor_exact (AdicCompletion I P) q.exact_subtype_ker_map hq
  rw [← hy, ← heq]
  exact (hright ((q.ker.subtype.rTensor (AdicCompletion I P)) w)).mpr ⟨w, rfl⟩

/-- Noether 基底上の有限加群と平坦加群について、比較写像は全単射。 -/
theorem adicCompletionTensorComparison_bijective [IsNoetherianRing A]
    [Module.Finite A N] [Module.Flat A P] :
    Function.Bijective (adicCompletionTensorComparison I N P) :=
  ⟨adicCompletionTensorComparison_injective I N P,
    adicCompletionTensorComparison_surjective I N P⟩

/-- 有限加群と平坦加群についての、自然な比較写像による完備化との交換同型。 -/
def adicCompletionTensorEquiv [IsNoetherianRing A] [Module.Finite A N] [Module.Flat A P] :
    N ⊗[A] AdicCompletion I P ≃ₗ[A] AdicCompletion I (N ⊗[A] P) :=
  LinearEquiv.ofBijective (adicCompletionTensorComparison I N P)
    (adicCompletionTensorComparison_bijective I N P)

end AdicCompletionTensor

section AdicCompletionTorsionTensor

open TensorProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {R C M : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module R M]

/-- I で消える加群とのテンソル積では、I の拡張イデアルの元が左因子にあると零となる。 -/
theorem tmul_eq_zero_of_mem_map_annihilator (I : Ideal R)
    (hM : Module.IsTorsionBySet R M I) (c : C)
    (hc : c ∈ I.map (algebraMap R C)) (m : M) : c ⊗ₜ[R] m = 0 := by
  rw [Ideal.map] at hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨r, hr, rfl⟩ := hc
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      hM (x := m) (a := ⟨r, hr⟩), tmul_zero]
  | zero => exact zero_tmul _ _
  | add x y _ _ hx hy => rw [add_tmul, hx, hy, add_zero]
  | smul c x _ hx =>
    change (c • x) ⊗ₜ[R] m = 0
    rw [← smul_tmul', hx, smul_zero]

/-- I の冪で消える加群を完備化へ送る標準テンソル写像は全単射。
逆向きの評価は完備化の開イデアル商を経由して構成する。 -/
theorem adicCompletion_tensor_one_bijective (I : Ideal R) (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  let Q := R ⧸ I ^ n
  let : Module Q M := hM.module
  let φ := adicCompletionOpenQuotientMap I (I ^ n) n le_rfl
  let : Module (AdicCompletion I R) M := Module.compHom M φ.toRingHom
  let : IsScalarTower R (AdicCompletion I R) M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change φ (algebraMap R (AdicCompletion I R) r) • m = r • m
    rw [adicCompletionOpenQuotientMap_algebraMap]
    exact hM.mk_smul r m
  let E : (AdicCompletion I R) ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift (Algebra.lsmul R R M (A := AdicCompletion I R)).toLinearMap
  have hleft : Function.LeftInverse E (TensorProduct.mk R (AdicCompletion I R) M 1) := by
    intro m
    change (1 : AdicCompletion I R) • m = m
    exact one_smul _ _
  refine ⟨hleft.injective, ?_⟩
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (φ c)
    have hd : c - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
      rw [← adicCompletionOpenQuotientMap_ker I (I ^ n) n le_rfl hI]
      change φ (c - algebraMap R (AdicCompletion I R) r) = 0
      rw [map_sub, adicCompletionOpenQuotientMap_algebraMap]
      exact sub_eq_zero.mpr hr.symm
    have ht := tmul_eq_zero_of_mem_map_annihilator (I ^ n) hM _ hd m
    rw [sub_tmul, sub_eq_zero] at ht
    refine ⟨r • m, ?_⟩
    change (1 : AdicCompletion I R) ⊗ₜ[R] (r • m) = c ⊗ₜ[R] m
    rw [ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨mx, hmx⟩ := hx
    obtain ⟨my, hmy⟩ := hy
    exact ⟨mx + my, by rw [map_add, hmx, hmy]⟩

/-- 冪ねじれ加群への完備化の基底変更を、基底環上の線形同値として公開する。 -/
def adicCompletionTorsionTensorEquiv (I : Ideal R) (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    (AdicCompletion I R) ⊗[R] M ≃ₗ[R] M :=
  (LinearEquiv.ofBijective (TensorProduct.mk R (AdicCompletion I R) M 1)
    (adicCompletion_tensor_one_bijective I hI n hM)).symm

end AdicCompletionTorsionTensor

section AdicCompletionFlatQuotient

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

/-- 平坦代数の商は、基底の同じイデアルによる商上で平坦。 -/
theorem flat_quotient_of_flat_algebra [Module.Flat B S] (I : Ideal B) :
    Module.Flat (B ⧸ I) (S ⧸ I.map (algebraMap B S)) :=
  (Module.Flat.equiv_iff
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv).mpr inferInstance

/-- 有限生成イデアルに沿う完備化の全冪商は、元の代数の平坦性から平坦となる。
Noether性は不要。完備化C自体のB上の平坦性はこの定理の結論ではない。 -/
theorem adicCompletionBasePowQuotient_flat [Module.Flat B S]
    (I : Ideal B) (hI : I.FG) (n : ℕ) :
    let C := AdicCompletion (I.map (algebraMap B S)) S
    Module.Flat (B ⧸ (I ^ n)) (C ⧸ (I ^ n).map (algebraMap B C)) :=
  (Module.Flat.equiv_iff (adicCompletionBasePowQuotientEquiv (S := S) I hI n).toLinearEquiv).mpr
    (flat_quotient_of_flat_algebra (S := S) (I ^ n))

end AdicCompletionFlatQuotient

section AdicCompletionScalarRestriction

open Submodule
variable {A S M : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (I : Ideal A)

/-- 各次数の冪商の、係数制限による同型。 -/
def adicCompletionScalarQuotientEquiv (n : ℕ) :
    (M ⧸ ((I.map (algebraMap A S)) ^ n • (⊤ : Submodule S M))) ≃ₗ[A]
      (M ⧸ (I ^ n • (⊤ : Submodule A M))) :=
  (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    (Submodule.quotEquivOfEq _ _ (by
      rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq]
      simp))

@[simp] theorem adicCompletionScalarQuotientEquiv_mk (n : ℕ) (m : M) :
    adicCompletionScalarQuotientEquiv (S := S) I n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  simp [adicCompletionScalarQuotientEquiv]

/-- 冪商の比較は逆極限の遷移写像と両立する。 -/
theorem adicCompletionScalarQuotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ ((I.map (algebraMap A S)) ^ n • (⊤ : Submodule S M))) :
    adicCompletionScalarQuotientEquiv (S := S) I m
      (AdicCompletion.transitionMap (I.map (algebraMap A S)) M h x) =
    AdicCompletion.transitionMap I M h
      (adicCompletionScalarQuotientEquiv (S := S) I n x) := by
  induction x using Submodule.Quotient.induction_on
  simp [AdicCompletion.transitionMap, Submodule.factorPow]

/-- 拡張イデアルによる完備化と、基底のイデアルによる加群の完備化は A 線形同型。 -/
def adicCompletionScalarRestrictionEquiv :
    AdicCompletion (I.map (algebraMap A S)) M ≃ₗ[A] AdicCompletion I M where
  toFun x := ⟨fun n ↦ adicCompletionScalarQuotientEquiv (S := S) I n (x.val n), by
    intro m n h
    rw [← adicCompletionScalarQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n ↦ (adicCompletionScalarQuotientEquiv (S := S) I n).symm (x.val n), by
    intro m n h
    apply (adicCompletionScalarQuotientEquiv (S := S) I m).injective
    rw [adicCompletionScalarQuotientEquiv_transition]
    simp [x.property h]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    simp
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    simp
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    change adicCompletionScalarQuotientEquiv (S := S) I n (x.val n + y.val n) = _
    exact map_add _ _ _
  map_smul' a x := by
    apply AdicCompletion.ext
    intro n
    change adicCompletionScalarQuotientEquiv (S := S) I n (a • x.val n) = _
    exact map_smul _ _ _

/-- 係数制限の比較は元の加群からの標準写像を保つ。 -/
@[simp] theorem adicCompletionScalarRestrictionEquiv_of (m : M) :
    adicCompletionScalarRestrictionEquiv (S := S) I
      (AdicCompletion.of (I.map (algebraMap A S)) M m) = AdicCompletion.of I M m := by
  apply AdicCompletion.ext
  intro n
  exact adicCompletionScalarQuotientEquiv_mk (S := S) I n m

/-- 各次数の評価と比較が両立する。 -/
@[simp] theorem adicCompletionScalarRestrictionEquiv_eval (n : ℕ)
    (x : AdicCompletion (I.map (algebraMap A S)) M) :
    AdicCompletion.eval I M n (adicCompletionScalarRestrictionEquiv (S := S) I x) =
      adicCompletionScalarQuotientEquiv (S := S) I n
        (AdicCompletion.eval (I.map (algebraMap A S)) M n x) := rfl

end AdicCompletionScalarRestriction

section AdicCompletionFlat

/-- Noether 環上の平坦加群のイデアル進完備化は、同じ基底環上で平坦。
加群の有限性や前完備性は不要。 -/
theorem flat_adicCompletion_of_flat
    {A P : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup P] [Module A P] [Module.Flat A P] (I : Ideal A) :
    Module.Flat A (AdicCompletion I P) := by
  apply ((Module.Flat.tfae_equational_criterion A (AdicCompletion I P)).out 1 2).mpr
  intro J
  have hinj := (adicCompletion_rTensor_injective_of_finite I J.subtype
    (Submodule.injective_subtype J) (P := P)).comp
    (adicCompletionTensorComparison_injective I J P)
  change Function.Injective ((AdicCompletion.map I (J.subtype.rTensor P)).restrictScalars A ∘ₗ
    adicCompletionTensorComparison I J P) at hinj
  rw [adicCompletionTensorComparison_natural] at hinj
  exact Function.Injective.of_comp hinj

/-- Noether 基底上の平坦代数を、基底から拡張したイデアルで完備化しても基底上平坦。
代数 S 自身の Noether 性・有限性・局所性は不要。 -/
theorem flat_adicCompletion_algebra_of_flat
    {A S : Type u} [CommRing A] [IsNoetherianRing A]
    [CommRing S] [Algebra A S] [Module.Flat A S] (I : Ideal A) :
    Module.Flat A (AdicCompletion (I.map (algebraMap A S)) S) :=
  (Module.Flat.equiv_iff (adicCompletionScalarRestrictionEquiv (S := S) (M := S) I)).mpr
    (flat_adicCompletion_of_flat I)

end AdicCompletionFlat

end SerrePositivity
