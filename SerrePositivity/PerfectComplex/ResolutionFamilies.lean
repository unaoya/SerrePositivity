module

public import SerrePositivity.HomologicalAlgebra.ControlledResolution
public import SerrePositivity.HomologicalAlgebra.UniformNullHomotopy
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# 有限長加群の族の一様な自由分解

## 概要

剰余体の固定分解から、加群の族を共通の次数範囲にある有限自由複体の族に持ち上げる。
各項の階数の等式を使い、長さの `O(s)`・`o(s)` 評価を階数の同じ評価へ移す。
元の加群を共通の冪で消せば、分解にも共通の冪が零ホモトピックに作用する。

## 方針と規約

`ControlledResolution` の存在定理を各加群に適用して分解を選ぶ。
選び方に依存せず同じ下限と階数公式を満たすので、族に関する一様性が保たれる。
次数は `[-d, 0]`、ホモロジーの消去指数は `N`、零ホモトピーの指数は `N * (d + 1)`。
漸近評価は通常の `atTop` に関するものであり、超フィルターは使わない。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing Filter Asymptotics

namespace SerrePositivity

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- 有限長加群の族には共通の次数範囲 `[-d, 0]` をもつ有限自由分解の族がある。
各項の階数は長さと固定された剰余体の分解の階数の積になる。 -/
theorem exists_uniform_free_resolutions {κ : Type*}
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
    (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
    (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
    (M : κ → ModuleCat.{u} A) (hM : ∀ k, IsFiniteLength A (M k)) :
    ∃ P : κ → CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ k, Nonempty (IsResolutionOf (P k) (M k))) ∧
      (∀ k i, Module.Free A ((P k).X i)) ∧ (∀ k i, Module.Finite A ((P k).X i)) ∧
      (∀ k i, (i < -(d : ℤ) ∨ 0 < i) → IsZero ((P k).X i)) ∧
      ∀ k i, Module.finrank A ((P k).X i) =
        (Module.length A (M k)).toNat * Module.finrank A (K.X i) := by
  choose P hres hfree hfinite hbound hrank using
    fun k ↦ exists_free_resolution_length_mul K hK hKf hKn (-(d : ℤ)) hKb (M k) (hM k)
  refine ⟨P, hres, hfree, hfinite, ?_, hrank⟩
  intro k i hi
  rcases hi with hi | hi
  · exact hbound k i hi
  · exact (hres k).some.isZero_X i hi

/-- 階数公式を満たす分解の族の各項を、その個数の環の直和と同一視する。
前段の Koszul 長さ評価に渡す有限基底の同型を与える。 -/
theorem resolutionFamily_term_iso {κ : Type*}
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : κ → ModuleCat.{u} A)
    (P : κ → CochainComplex (ModuleCat.{u} A) ℤ)
    (hfree : ∀ k i, Module.Free A ((P k).X i))
    (hfinite : ∀ k i, Module.Finite A ((P k).X i))
    (hrank : ∀ k i, Module.finrank A ((P k).X i) =
      (Module.length A (M k)).toNat * Module.finrank A (K.X i)) (k : κ) (i : ℤ) :
    Nonempty ((P k).X i ≅ ModuleCat.of A
      (Fin ((Module.length A (M k)).toNat * Module.finrank A (K.X i)) → A)) := by
  have := hfree k i
  have := hfinite k i
  exact ⟨(Module.finBasisOfFinrankEq A ((P k).X i) (hrank k i)).equivFun.toModuleIso⟩

omit [IsLocalRing A] in
/-- 加群列の長さが `O(s)` で、分解の階数公式が成立すれば、各項の階数も `O(s)`。
固定分解の項の階数による定数倍として評価する。 -/
theorem resolutionFamily_rank_isBigO
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ℕ → ModuleCat.{u} A)
    (P : ℕ → CochainComplex (ModuleCat.{u} A) ℤ)
    (hrank : ∀ k i, Module.finrank A ((P k).X i) =
      (Module.length A (M k)).toNat * Module.finrank A (K.X i))
    (s : ℕ → ℝ) (hM : (fun k ↦ ((Module.length A (M k)).toNat : ℝ)) =O[atTop] s)
    (i : ℤ) : (fun k ↦ (Module.finrank A ((P k).X i) : ℝ)) =O[atTop] s := by
  apply (hM.const_mul_left (Module.finrank A (K.X i) : ℝ)).congr_left
  intro k
  rw [hrank k i, Nat.cast_mul, mul_comm]

omit [IsLocalRing A] in
/-- 加群列の長さが `o(s)` なら、階数公式を満たす分解の各項の階数も `o(s)`。
長さで小さい加群列を、ランクで小さい自由複体列に持ち上げる接続。 -/
theorem resolutionFamily_rank_isLittleO
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (M : ℕ → ModuleCat.{u} A)
    (P : ℕ → CochainComplex (ModuleCat.{u} A) ℤ)
    (hrank : ∀ k i, Module.finrank A ((P k).X i) =
      (Module.length A (M k)).toNat * Module.finrank A (K.X i))
    (s : ℕ → ℝ) (hM : (fun k ↦ ((Module.length A (M k)).toNat : ℝ)) =o[atTop] s)
    (i : ℤ) : (fun k ↦ (Module.finrank A ((P k).X i) : ℝ)) =o[atTop] s := by
  apply (hM.const_mul_left (Module.finrank A (K.X i) : ℝ)).congr_left
  intro k
  rw [hrank k i, Nat.cast_mul, mul_comm]

omit [IsLocalRing A] in
/-- 加群を消すスカラーは、その分解の全ホモロジーを消す。
零次では分解の同型で移し、他の次数ではホモロジーが零であることを使う。 -/
lemma resolution_homology_annihilated
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} A)
    (hP : IsResolutionOf P M) (r : A) (hr : r • 𝟙 M = 0) (i : ℤ) :
    r • 𝟙 (P.homology i) = 0 := by
  by_cases hi : i = 0
  · subst i
    rw [← cancel_mono hP.homologyZeroIso.hom]
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
      zero_comp, comp_zero] using congrArg (fun f : M ⟶ M ↦ hP.homologyZeroIso.hom ≫ f) hr
  · exact (hP.isZero_homology i hi).eq_of_src _ _

omit [IsLocalRing A] in
/-- 共通の範囲 `[-d, 0]` の分解の族で、加群を `x_j^N` が一様に消すなら、
`x_j^(N * (d + 1))` は分解に一様に零ホモトピックに作用する。 -/
theorem resolutionFamily_uniform_nullHomotopies {κ ι : Type*}
    (M : κ → ModuleCat.{u} A) (P : κ → CochainComplex (ModuleCat.{u} A) ℤ)
    (hres : ∀ k, Nonempty (IsResolutionOf (P k) (M k)))
    (d : ℕ) (hbound : ∀ k i, (i < -(d : ℤ) ∨ 0 < i) → IsZero ((P k).X i))
    (x : ι → A) (N : ℕ) (hM : ∀ k j, x j ^ N • 𝟙 (M k) = 0) :
    ∀ k j, Nonempty (Homotopy (smulId (x j ^ (N * (d + 1))) (P k)) 0) := by
  apply uniform_nullHomotopies_of_homology_annihilated P x N (-(d : ℤ)) (d + 1)
    (fun k ↦ (hres k).some.projective)
  · intro k i hi
    exact hbound k i (by omega)
  · intro k j i
    exact resolution_homology_annihilated (P k) (M k) (hres k).some (x j ^ N) (hM k j) i

end SerrePositivity
