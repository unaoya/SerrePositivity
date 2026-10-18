module

public import SerrePositivity.KST.DerivedGeometry.InjectiveFactorExpansion
public import SerrePositivity.KST.DerivedGeometry.PullbackFactorSection

/-!
概要：非有界の単射準同型拡大の各成分は injective な部分対象を経由する。
方針：評価関手の pullback 保存と contractible 全射の各項の切断を使う。
規約：拡大先の全ての項が injective とは主張しない。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の一工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C] (K : CochainComplex C ℤ)

/--
概要：各項 injective な埋め込み先から準同型拡大の同じ次数への単射。
方針：余核への各項分裂全射の pullback へ、評価後に切断を作る。
規約：射は指定された次数のもの。
使われ方：Stacks Lemma 19.12.5、TT §3 の injective 部分対象。
-/
def injectiveFactorExpansionFactor (n : ℤ) :
    (termInjectiveEnvelope K).X n ⟶ (injectiveFactorExpansion K).X n :=
  pullbackFactorSection (HomologicalComplex.eval C (.up ℤ) n) (injectiveEnvelopeShortComplex K)
    (contractibleEpi (cokernel (termInjectiveEnvelopeι K)))
    (contractibleEpiSection (cokernel (termInjectiveEnvelopeι K)) n)
    (contractibleEpiSection_comp (cokernel (termInjectiveEnvelopeι K)) n)

/--
概要：各項 injective な対象からの因子は単射。
方針：評価後の pullback の切断が単射であることを適用する。
規約：実際の拡大の次数別の部分対象。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の injective 部分対象。
-/
instance injectiveFactorExpansionFactor_mono (n : ℤ) : Mono (injectiveFactorExpansionFactor K n) :=
  pullbackFactorSection_mono (HomologicalComplex.eval C (.up ℤ) n) (injectiveEnvelopeShortComplex K)
    (contractibleEpi (cokernel (termInjectiveEnvelopeι K)))
    (contractibleEpiSection (cokernel (termInjectiveEnvelopeι K)) n)
    (contractibleEpiSection_comp (cokernel (termInjectiveEnvelopeι K)) n)

/--
概要：単射準同型拡大の各成分は injective 部分対象を経由する。
方針：pullback の切断の因子化公式を各次数の評価関手へ適用する。
規約：因子化の中間対象は構成済みの各項 injective な双積。
使われ方：Stacks Lemma 19.12.5、TT §3・§8、Toën §3.2 の超限反復の一工程。
-/
lemma injectiveFactorExpansion_component_factor (n : ℤ) :
    (termInjectiveEnvelopeι K).f n ≫ injectiveFactorExpansionFactor K n =
      (injectiveFactorExpansionι K).f n :=
  pullbackFactorSection_factor (HomologicalComplex.eval C (.up ℤ) n) (injectiveEnvelopeShortComplex K)
    (contractibleEpi (cokernel (termInjectiveEnvelopeι K)))
    (contractibleEpiSection (cokernel (termInjectiveEnvelopeι K)) n)
    (contractibleEpiSection_comp (cokernel (termInjectiveEnvelopeι K)) n)

end SerrePositivity.KST.DerivedGeometry
