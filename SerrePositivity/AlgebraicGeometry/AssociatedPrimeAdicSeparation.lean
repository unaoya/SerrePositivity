module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Filtration

/-!
概要：KST §5、Stacks 05DL の随伴素イデアルの条件によるイデアル進分離性。
方針：Artin–Rees の冪共通部分の判定と、元の零化イデアルを含む随伴素イデアルを使う。
規約：全ての随伴素イデアルがイデアルと互いに素にならないことを要求する。
使われ方：有限テンソル試験における完備化への単射性。
-/

@[expose] public section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：イデアルと互いに素な随伴素イデアルがなければ、有限加群の冪共通部分は零。
方針：rx=x となる r を Artin–Rees から取り、非零元の随伴素イデアルで 1 を生成して矛盾する。
規約：KST §5、Stacks 05DL, Lemma 38.8.3、Noether 環上の有限加群。
使われ方：イデアル進分離性と完備化への単射性。
-/
theorem iInf_pow_smul_eq_bot_of_associatedPrimes
    {S N : Type u} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] (J : Ideal S)
    (hAss : ∀ p : Ideal S, p ∈ associatedPrimes S N → J ⊔ p ≠ ⊤) :
    (⨅ n : ℕ, J ^ n • (⊤ : Submodule S N)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  by_contra hx0
  obtain ⟨r, hr⟩ := (J.mem_iInf_smul_pow_eq_bot_iff x).mp hx
  obtain ⟨p, hp, hxp⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S x hx0
  have hsub : (1 - r.val) ∈ p := by
    apply hxp
    rw [Submodule.mem_colon_singleton]
    change (1 - r.val) • x = 0
    rw [sub_smul, one_smul, hr, sub_self]
  have h1 : (1 : S) ∈ J ⊔ p := by
    have hsum := (J ⊔ p).add_mem
      (show r.val ∈ J ⊔ p from (le_sup_left : J ≤ J ⊔ p) r.property)
      (show 1 - r.val ∈ J ⊔ p from (le_sup_right : p ≤ J ⊔ p) hsub)
    simpa only [add_comm r.val, sub_add_cancel] using hsum
  exact hAss p hp ((Ideal.eq_top_iff_one _).mpr h1)

/--
概要：有限加群の随伴素イデアルの条件からイデアル進分離性を得る。
方針：冪共通部分が零であることを分離性の定義へ移す。
規約：KST §5、Stacks 05DL、随伴素イデアルの条件は元のイデアルとの和で表す。
使われ方：標準完備化写像の単射性。
-/
theorem isHausdorff_of_associatedPrimes
    {S N : Type u} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] (J : Ideal S)
    (hAss : ∀ p : Ideal S, p ∈ associatedPrimes S N → J ⊔ p ≠ ⊤) :
    IsHausdorff J N := by
  constructor
  intro x hx
  have hm : x ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule S N)) :=
    (Submodule.mem_iInf (fun n : ℕ => J ^ n • (⊤ : Submodule S N))).mpr
      (fun n => SModEq.zero.mp (hx n))
  rw [iInf_pow_smul_eq_bot_of_associatedPrimes J hAss] at hm
  exact hm

/--
概要：随伴素イデアルの条件を満たす有限加群の標準完備化写像は単射。
方針：証明した分離性を標準完備化写像の単射性へ渡す。
規約：KST §5、Stacks 05DL、基礎環自体の完備性は不要。
使われ方：完備化への普遍単射性の有限試験。
-/
theorem adicCompletion_of_injective_of_associatedPrimes
    {S N : Type u} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] (J : Ideal S)
    (hAss : ∀ p : Ideal S, p ∈ associatedPrimes S N → J ⊔ p ≠ ⊤) :
    Function.Injective (AdicCompletion.of J N) := by
  let := isHausdorff_of_associatedPrimes J hAss
  exact AdicCompletion.of_injective J N

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
