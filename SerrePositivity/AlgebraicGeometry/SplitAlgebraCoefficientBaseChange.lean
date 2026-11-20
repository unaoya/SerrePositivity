module

public import SerrePositivity.AlgebraicGeometry.SplitAlgebraTensorCoefficients
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の係数イデアルと任意の基底変更。
方針：基底変更した分裂表示で、代数イデアルの像の生成元の係数を計算する。
規約：係数環の平坦性は不要で、元の分裂表示を明示的に入力する。
使われ方：係数中心の blowup 後の拡大と代数側の小行列式イデアルを比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R B C ι : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/--
概要：代数イデアルの基底変更の係数イデアルは、元の係数イデアルの基底変更と一致する。
方針：分裂した係数表示を基底変更し、イデアルの像の生成元で係数を比較する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、代数への写像はテンソル積の右包含。
使われ方：平坦化中心のチャートで小行列式の全係数が同じ主イデアルに入ることを得る。
-/
theorem splitAlgebraCoefficientIdeal_baseChange
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (J : Ideal B) :
    splitAlgebraCoefficientIdeal (splitAlgebraTensorEmbedding (C := C) e)
        (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom) =
      (splitAlgebraCoefficientIdeal e J).map (algebraMap R C) := by
  classical
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  let φ : B →+* C ⊗[R] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hcoeff : ∀ b i, e' (φ b) i = algebraMap R C (e b i) := by
    intro b i
    change splitAlgebraTensorEmbedding e ((1 : C) ⊗ₜ[R] b) i = algebraMap R C (e b i)
    simpa only [mul_one] using splitAlgebraTensorEmbedding_tmul e (1 : C) b i
  have hspan : splitAlgebraCoefficientIdeal e' (J.map φ) =
      finsuppCoefficientIdeal (e' '' (φ '' (J : Set B))) :=
    splitAlgebraCoefficientIdeal_span e' p' hs (φ '' (J : Set B))
  change splitAlgebraCoefficientIdeal e' (J.map φ) =
    (splitAlgebraCoefficientIdeal e J).map (algebraMap R C)
  apply le_antisymm
  · rw [hspan]
    apply (finsuppCoefficientIdeal_le_iff _ _).mpr
    rintro x ⟨z, ⟨b, hb, rfl⟩, rfl⟩ i
    rw [hcoeff]
    exact Ideal.mem_map_of_mem _
      (mem_finsuppCoefficientIdeal (s := e '' (J : Set B)) ⟨b, hb, rfl⟩ i)
  · rw [Ideal.map_le_iff_le_comap]
    apply (finsuppCoefficientIdeal_le_iff _ _).mpr
    rintro x ⟨b, hb, rfl⟩ i
    change algebraMap R C (e b i) ∈ splitAlgebraCoefficientIdeal e' (J.map φ)
    rw [← hcoeff]
    exact mem_finsuppCoefficientIdeal (s := e' '' (J.map φ : Set (C ⊗[R] B)))
      ⟨φ b, Ideal.mem_map_of_mem φ hb, rfl⟩ i

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
