module

public import SerrePositivity.KST.DerivedGeometry.ContractibleComplexEpi
public import SerrePositivity.KST.DerivedGeometry.ShortExactPullback
public import SerrePositivity.KST.DerivedGeometry.AcyclicCokernelQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：任意の非有界複体の単射準同型な拡大を pullback で構成する。
方針：各項 injective な複体への単射の余核を、contractible な複体からの全射で引き戻す。
規約：拡大先自体が各項 injective や K-injective であるとは主張しない。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の非有界分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C] (K : CochainComplex C ℤ)

/--
概要：各項 injective な複体への単射とその余核の短複体。
方針：複体の圏で実際の余核を取る。
規約：非有界。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型拡大の入力。
-/
def injectiveEnvelopeShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (termInjectiveEnvelopeι K) (cokernel.π (termInjectiveEnvelopeι K))
    (cokernel.condition _)

/--
概要：injective 埋め込みと余核の短複体は短完全。
方針：余核の普遍性と既証の単射性を使う。
規約：各項の射から複体の圏の単射性を得てから適用する。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型拡大。
-/
lemma injectiveEnvelopeShortComplex_shortExact : (injectiveEnvelopeShortComplex K).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (termInjectiveEnvelopeι K))
  mono_f := termInjectiveEnvelopeι_mono K
  epi_g := by change Epi (cokernel.π (termInjectiveEnvelopeι K)); infer_instance

/--
概要：余核への contractible 全射の引き戻しから作る短複体。
方針：元の埋め込みの短完全列をその右端で引き戻す。
規約：第三項は明示的に contractible。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の非有界準同型拡大。
-/
def injectiveFactorExpansionShortComplex : ShortComplex (CochainComplex C ℤ) :=
  shortComplexPullback (injectiveEnvelopeShortComplex K)
    (contractibleEpi (cokernel (termInjectiveEnvelopeι K)))

/--
概要：pullback で得た拡大の短複体は短完全。
方針：証明済みの短完全列の pullback の一般補題を適用する。
規約：元の対象は第一項の K。
使われ方：Stacks Lemma 19.12.5、TT §3 の準同型判定。
-/
lemma injectiveFactorExpansionShortComplex_shortExact :
    (injectiveFactorExpansionShortComplex K).ShortExact :=
  shortComplexPullback_shortExact _ _ (injectiveEnvelopeShortComplex_shortExact K)

/--
概要：非有界複体の明示的な拡大先。
方針：構成した短完全列の中央対象を使う。
規約：K-injectivity はまだ主張しない。
使われ方：Stacks Lemma 19.12.5、TT §3・§8 の超限反復の一工程。
-/
def injectiveFactorExpansion : CochainComplex C ℤ := (injectiveFactorExpansionShortComplex K).X₂

/--
概要：元の複体から実際の拡大への鎖写像。
方針：短完全列の第一射を使う。
規約：元の複体を同型類だけでなく保持する。
使われ方：Stacks Lemma 19.12.5、TT §3 の超限反復の遷移射。
-/
def injectiveFactorExpansionι : K ⟶ injectiveFactorExpansion K :=
  (injectiveFactorExpansionShortComplex K).f

/--
概要：拡大への鎖写像は単射。
方針：構成済みの短完全性を使う。
規約：非有界。
使われ方：Stacks Lemma 19.12.5、TT §3 の極限での単射性。
-/
instance injectiveFactorExpansionι_mono : Mono (injectiveFactorExpansionι K) :=
  (injectiveFactorExpansionShortComplex_shortExact K).mono_f

/--
概要：拡大への鎖写像は準同型。
方針：短完全列の第三項の縮約から全コホモロジーの比較を得る。
規約：有界性や未証明の比較を仮定しない。
使われ方：Stacks Lemma 19.12.5、TT §3・§8、Toën §3.2 の非有界分解の一工程。
-/
instance injectiveFactorExpansionι_quasiIso : QuasiIso (injectiveFactorExpansionι K) :=
  shortExact_quasiIso_f_of_acyclic (injectiveFactorExpansionShortComplex K)
    (injectiveFactorExpansionShortComplex_shortExact K) (contractibleEpiSource_acyclic _)

end SerrePositivity.KST.DerivedGeometry
