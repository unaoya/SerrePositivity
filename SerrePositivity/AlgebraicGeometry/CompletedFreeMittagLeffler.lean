module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.CompletedFreeFiniteTensor
public import SerrePositivity.AlgebraicGeometry.FiniteTensorTest
public import SerrePositivity.AlgebraicGeometry.NoetherianScalarProduct
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor

/-!
概要：KST §5、Stacks 05DJ, Lemma 38.8.1 の自由加群の完備化の Mittag–Leffler 性。
方針：完備な Noether 環の積への普遍単射性と、積の Mittag–Leffler 性を使う。
規約：自由加群の基底は任意の集合。完備化の平坦性は既存の環論の定理を利用する。
使われ方：剰余が射影的な平坦加群の完備化に関する 05DK の自由全射側の入力。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：完備な Noether 環上で、自由完備化の積埋め込みは任意の左テンソルで単射。
方針：有限生成な試験加群の場合と係数環の積の平坦性を有限試験の判定へ渡す。
規約：KST §5、Stacks 05BC・05DJ、試験加群の有限性も平坦性も要求しない。
使われ方：積の Mittag–Leffler 性を自由完備化へ降下する。
-/
theorem completedFreeEmbedding_lTensor_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (A N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective ((completedFreeEmbedding I A).lTensor N) := by
  let := flat_pi_of_noetherian R A
  exact lTensor_injective_of_finite_tests (completedFreeEmbedding I A)
    (fun Q _ _ _ => completedFreeEmbedding_lTensor_injective_of_finite I A Q) N

/--
概要：自由完備化の積埋め込みは、任意の右テンソルでも単射。
方針：左テンソルの単射性をテンソル交換同型で移す。
規約：KST §5、Stacks 05BC・05DJ、実際の埋め込みの普遍単射性。
使われ方：普遍単射部分加群への Mittag–Leffler 性の降下。
-/
theorem completedFreeEmbedding_rTensor_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (A N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective ((completedFreeEmbedding I A).rTensor N) :=
  ((completedFreeEmbedding I A).lTensor_inj_iff_rTensor_inj N).mp
    (completedFreeEmbedding_lTensor_injective I A N)

/--
概要：完備な Noether 環上で任意の自由加群の完備化は Mittag–Leffler。
方針：係数環の積の Mittag–Leffler 性を、構成した普遍単射な積埋め込みへ戻す。
規約：KST §5、Stacks 05DJ, Lemma 38.8.1 の自由加群部分。
使われ方：自由全射の完備化の分裂から一般の平坦加群の完備化へ進む。
-/
theorem isModuleMittagLeffler_completedFree
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (A : Type u) : IsModuleMittagLeffler R (AdicCompletion I (A →₀ R)) :=
  isModuleMittagLeffler_of_universally_injective (completedFreeEmbedding I A)
    (fun N _ _ => completedFreeEmbedding_rTensor_injective I A N)
    (isModuleMittagLeffler_pi_of_noetherian R A)

/--
概要：Noether 環上の任意の自由加群の完備化は基礎環上平坦。
方針：既存の環論の平坦加群の完備化定理を有限台自由加群へ適用する。
規約：KST §5、Stacks 05DJ、平坦性には基礎環の完備性は不要。
使われ方：自由完備化の平坦 Mittag–Leffler 性の平坦性側。
-/
theorem flat_completedFree
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A : Type u) :
    Module.Flat R (AdicCompletion I (A →₀ R)) :=
  SerrePositivity.flat_adicCompletion_of_flat I

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
