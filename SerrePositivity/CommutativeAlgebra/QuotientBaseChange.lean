module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Maps

/-! # イデアルによる商と係数拡大

任意の代数 `A → B` と `A` 加群 `M` について、
`(B ⊗ M)/(IB)(B ⊗ M) ≃ B ⊗ (M/IM)` を `B` 線形同型として構成する。
テンソル積の右完全性だけを使い、平坦性は仮定しない。
-/

@[expose] public section

universe u

open TensorProduct

namespace SerrePositivity

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type u) [AddCommGroup M] [Module A M]

set_option backward.isDefEq.respectTransparency false

/-- `IM` の係数拡大は `IB` による積部分加群に一致する。 -/
lemma baseChange_smul_top (I : Ideal A) :
    (I • (⊤ : Submodule A M)).baseChange B =
      I.map (algebraMap A B) • (⊤ : Submodule B (B ⊗[A] M)) := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change (1 : B) ⊗ₜ[A] x ∈ (I.map (algebraMap A B) • (⊤ : Submodule B (B ⊗[A] M)))
    refine Submodule.smul_induction_on hx (fun a ha m _ => ?_)
      (fun x y hx hy => ?_)
    · change (1 : B) ⊗ₜ[A] (a • m) ∈ _
      rw [tmul_smul, ← algebraMap_smul B a]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    · simpa only [tmul_add] using Submodule.add_mem _ hx hy
  · rw [Ideal.map, Submodule.span_smul_eq, Submodule.set_smul_le_iff]
    rintro _ x ⟨a, ha, rfl⟩ hx
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      rw [algebraMap_smul, ← tmul_smul]
      exact Submodule.tmul_mem_baseChange_of_mem _
        (Submodule.smul_mem_smul ha Submodule.mem_top)
    | add x y hx hy => simpa [smul_add] using Submodule.add_mem _ hx hy

/-- イデアルによる商と係数拡大の両立。 -/
noncomputable def quotientBaseChangeEquiv (I : Ideal A) :
    ((B ⊗[A] M) ⧸ (I.map (algebraMap A B) • ⊤ : Submodule B (B ⊗[A] M))) ≃ₗ[B]
      B ⊗[A] (M ⧸ (I • ⊤ : Submodule A M)) := by
  let N : Submodule A M := I • ⊤
  let f := N.mkQ.baseChange B
  have hker : LinearMap.ker f = N.baseChange B := by
    apply Submodule.restrictScalars_injective A
    exact lTensor_mkQ B N
  rw [← baseChange_smul_top A B M I, ← hker]
  exact f.quotKerEquivOfSurjective (N.mkQ.baseChange_surjective B N.mkQ_surjective)

end SerrePositivity
