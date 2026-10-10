module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.RingTheory.KrullDimension.Module

/-!
# 交点重複度の一般的な入力

補題5.2の導出に用いる一般論を、命題値のクラスとして明示する。
`RegularResolution` は正則局所環上の分解の存在、`TorHomologicalAlgebra` は Tor の一般論、
`IntersectionAdditivity` は加法性、
`GenericBasis` は一般点での基底と余核の次元、`IntersectionVanishing` は消滅定理を受け持つ。
五つのクラスは合計7個の主張を仮定する。クラスの宣言自体は、その主張の証明ではない。

このファイルではインスタンスも公理も登録しない。利用側はクラスを仮定として受け取る。
Mathlib にある基礎定理から導ける候補と、大きな外部定理を区別して整備する必要がある。
正規化長さ、Galois 群、ノルム比較、補題5.2の結論は入力に含めない。
-/

public section

universe u

open CategoryTheory TensorProduct

namespace SerrePositivity.Inputs

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- 正則局所環上の有界有限自由分解の存在を受け取る入力。
Tor の比較や有限長性とは分け、正則性を必要とする主張だけを置く。 -/
class RegularResolution (R : Type u) [CommRing R] [IsRegularLocalRing R] : Prop where
  /-- 任意の有限生成 `R` 加群に、有界な有限自由コチェイン分解が存在するという仮定。 -/
  resolution : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i))

/-- Tor の計算と有限長性に関する一般論の入力。比較は可換環上、有限長性は Noether 環上の主張。
この二つはまだ証明していない。正則局所環上の分解の存在とは独立に仮定する。 -/
class TorHomologicalAlgebra (R : Type u) [CommRing R] : Prop where
  /-- 係数拡大した射影分解の `-i` 次ホモロジーを `R` に係数制限すると、
  通常の `Tor_i^R(T, M)` と線形同値になるという仮定。 -/
  ordinaryTorIso : ∀ (T : Type u) [CommRing T] [Algebra R T]
      (M : Type u) [AddCommGroup M] [Module R M]
      (F : CochainComplex (ModuleCat.{u} R) ℤ),
    IsResolutionOf F (ModuleCat.of R M) → ∀ i : ℕ,
      Nonempty (((ModuleCat.restrictScalars (algebraMap R T)).obj
        ((baseChange (algebraMap R T) F).homology (-(i : ℤ)))) ≃ₗ[R] TorModule R i T M)
  /-- 有限生成加群 `M, N` のテンソル積が有限長なら、各 `Tor_i^R(M, N)` も有限長となる仮定。 -/
  finiteTor : ∀ [IsNoetherianRing R] (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
      ∀ i : ℕ, Module.length R (TorModule R i M N) ≠ ⊤

/-- 交点重複度の各変数について、短完全列に沿う加法性を受け取る入力。
有限直和の評価は `FiniteExtension.lean` でこの二つの加法性から証明する。 -/
class IntersectionAdditivity : Prop where
  /-- 第1変数の短完全列に対する `χ` の加法性。中央の加群と第2変数のテンソル積は有限長とする。 -/
  add_left : ∀ (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    Module.length R (M₂ ⊗[R] N) ≠ ⊤ → chi R M₂ N = chi R M₁ N + chi R M₃ N
  /-- 第2変数の短完全列に対する `χ` の加法性。第1変数と中央の加群のテンソル積は有限長とする。 -/
  add_right : ∀ (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    Module.length R (M ⊗[R] N₂) ≠ ⊤ → chi R M N₂ = chi R M N₁ + chi R M N₃
/-- 一般点での基底と、その余核の次元低下に関する入力。
まだ証明していない。正規化長さや群作用の仮定は含まない。 -/
class GenericBasis : Prop where
  /-- 整域 `R/I` 上で正の階数をもつ有限生成加群に、同じ階数の自由加群を単射で入れ、
  余核の `R` 上の台の次元を `dim(R/I)` より小さくできるという仮定。 -/
  generic_basis : ∀ (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M] [Module.Finite (R ⧸ I) M],
    0 < Module.finrank (R ⧸ I) M →
    ∃ f : (Fin (Module.finrank (R ⧸ I) M) → R ⧸ I) →ₗ[R] M,
      Function.Injective f ∧
        Module.supportDim R (M ⧸ LinearMap.range f) < ringKrullDim (R ⧸ I)
/-- Roberts–Gillet–Soulé の交点重複度消滅定理を受け取る入力（論文 (5.1)）。
有限生成加群のテンソル積が有限長で、台の次元の和が環の次元より小さいとき `χ = 0` とする。 -/
class IntersectionVanishing : Prop where
  /-- テンソル積の有限長性と `dim M + dim N < dim R` のもとで、交点重複度を零とする仮定。 -/
  vanish : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N], Module.length R (M ⊗[R] N) ≠ ⊤ →
    Module.supportDim R M + Module.supportDim R N < ringKrullDim R → chi R M N = 0

end SerrePositivity.Inputs
