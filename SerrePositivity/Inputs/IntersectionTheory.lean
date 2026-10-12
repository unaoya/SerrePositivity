module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import SerrePositivity.HomologicalAlgebra.FiniteFreeResolution
public import SerrePositivity.HomologicalAlgebra.RegularLocalResolution
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.RingTheory.KrullDimension.Module

/-!
# 交点重複度で用いる正則局所環の定理と消滅定理

`regularResolution` は証明済みの正則パラメータの正則性から導く。
分解の構成は `HomologicalAlgebra/FiniteFreeResolution.lean` の一般定理を使う。
Roberts–Gillet–Soulé の消滅定理 `intersectionVanishing` は文献からの引用として
名前付きの `sorry` 定理に残す。利用先では各定理を明示的に適用する。

Tor の有限長性と交点重複度の左右の加法性は別ファイルで証明済み。
加法性で使う Tor の高次消滅は、ここで構成する有界有限自由分解による。
-/

public section

universe u

open CategoryTheory TensorProduct

namespace SerrePositivity.Inputs

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- 正則局所環上の有界有限自由分解の存在。極大イデアルの正則生成列を選び、
一般定理から自然数添字の有限自由分解を構成し、整数添字へ移す。
正則パラメータの正則性を含めて証明済み。 -/
theorem regularResolution (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i)) :=
  SerrePositivity.regularResolution R M

/-- Roberts–Gillet–Soulé の消滅定理（引用、未証明、論文 (5.1)）。
`M ⊗ N` が有限長で `dim Supp M + dim Supp N < dim R` なら交点重複度は零。
引用を名前付きの定理として明示し、利用先も `sorryAx` に依存する。 -/
theorem intersectionVanishing
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 := by
  sorry

end SerrePositivity.Inputs
