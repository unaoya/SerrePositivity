module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
概要：KST §5、Stacks 05BC, Lemma 15.28.1 の完備化した有限台関数の座標埋め込み。
方針：イデアル倍への所属を各座標で判定し、完備化の各剰余段階で単射性を示す。
規約：係数加群の完備性、Noether 性、イデアルの有限生成性は不要。
使われ方：自由加群の完備化から係数環の積への普遍単射性の座標側。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：有限台関数がイデアル倍に属することは、全係数が係数加群の同じイデアル倍に属することと同値。
方針：評価写像で一方向を示し、有限個の単一台関数の和で逆向きを示す。
規約：KST §5、Stacks 05BC、イデアルの有限生成性は不要。
使われ方：完備化の剰余段階を座標ごとに区別する。
-/
theorem finsupp_mem_ideal_smul_top_iff
    {R A N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (v : A →₀ N) :
    v ∈ J • (⊤ : Submodule R (A →₀ N)) ↔ ∀ a, v a ∈ J • (⊤ : Submodule R N) := by
  classical
  constructor
  · intro hv a
    exact (Submodule.smul_top_le_comap_smul_top J
      (Finsupp.lapply a : (A →₀ N) →ₗ[R] N)) hv
  · intro hv
    rw [← Finsupp.sum_single v]
    apply Submodule.sum_mem
    intro a _
    exact (Submodule.smul_top_le_comap_smul_top J
      (Finsupp.lsingle a : N →ₗ[R] (A →₀ N))) (hv a)

/--
概要：完備化した有限台関数を、各係数の完備化の族へ送る実際の線形写像。
方針：各座標評価を完備化し、基礎環上の線形写像として束ねる。
規約：KST §5、Stacks 05BC、完備化環上の作用は基礎環へ制限する。
使われ方：完備化した自由加群と係数環の積を比較する。
-/
def completedFinsuppCoordinates
    {R : Type*} [CommRing R] (I : Ideal R) (A N : Type*) [AddCommGroup N] [Module R N] :
    AdicCompletion I (A →₀ N) →ₗ[R] (A → AdicCompletion I N) :=
  LinearMap.pi (fun a => (AdicCompletion.map I (Finsupp.lapply a)).restrictScalars R)

/--
概要：完備化座標写像は元の有限台関数の各係数の標準完備化を返す。
方針：完備化写像の元の加群上での公式を使う。
規約：KST §5、Stacks 05BC、有限台関数からの標準写像を保つ。
使われ方：自由加群の完備化と元の係数の比較。
-/
theorem completedFinsuppCoordinates_of
    {R : Type*} [CommRing R] (I : Ideal R) (A N : Type*) [AddCommGroup N] [Module R N]
    (v : A →₀ N) :
    completedFinsuppCoordinates I A N (AdicCompletion.of I (A →₀ N) v) =
      fun a => AdicCompletion.of I N (v a) := by
  funext a
  exact AdicCompletion.map_of I (Finsupp.lapply a) v

/--
概要：完備化した有限台関数は全座標の完備化によって区別される。
方針：各剰余段階の代表元の全係数がイデアル冪に入ることから、代表元自体の消滅を導く。
規約：KST §5、Stacks 05BC、Noether 性・係数加群の有限性は不要。
使われ方：有限加群とのテンソル・完備化比較の標的の単射性。
-/
theorem completedFinsuppCoordinates_injective
    {R : Type*} [CommRing R] (I : Ideal R) (A N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (completedFinsuppCoordinates I A N) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have hvmem : v ∈ I ^ n • (⊤ : Submodule R (A →₀ N)) := by
    apply (finsupp_mem_ideal_smul_top_iff (I ^ n) v).mpr
    intro a
    have ha : AdicCompletion.map I (Finsupp.lapply a : (A →₀ N) →ₗ[R] N) x = 0 :=
      congrFun hx a
    have hn := congrArg (fun z : AdicCompletion I N => z.val n) ha
    rw [AdicCompletion.map_val_apply, ← hv, LinearMap.reduceModIdeal_apply] at hn
    have hmem : v a ∈ LinearMap.ker (I ^ n • (⊤ : Submodule R N)).mkQ := hn
    simpa only [Submodule.ker_mkQ] using hmem
  change x.val n = 0
  rw [← hv]
  change v ∈ LinearMap.ker (I ^ n • (⊤ : Submodule R (A →₀ N))).mkQ
  simpa only [Submodule.ker_mkQ] using hvmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
