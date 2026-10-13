module

public import SerrePositivity.CommutativeAlgebra.FlatTensorFiltration
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # 加群のテンソル積と完備化の標準比較

N⊗_A P̂ から (N⊗_A P)^ への写像を、各 n に対するテンソル写像の完備化で構成する。
この構成と自然性には有限性・Noether 性・平坦性を要求しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity
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

end SerrePositivity
