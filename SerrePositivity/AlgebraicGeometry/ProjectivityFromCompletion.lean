module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FibreAdicUniversalInjection
public import SerrePositivity.AlgebraicGeometry.CompletedFlatMittagLeffler
public import SerrePositivity.AlgebraicGeometry.CountableFlatMittagLefflerProjective
public import Mathlib.RingTheory.FiniteType

/-!
概要：KST §5、Stacks 05DP, Lemma 38.9.1 の完備化による射影性。
方針：ファイバー条件による普遍単射性と完備化の Mittag–Leffler 性を降下し、可算生成判定を使う。
規約：有限型代数上の有限加群の可算生成性は既に証明した定理を利用する。
使われ方：Stacks 05FS の平坦な有限表示代数の射影性の存在。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：最初の剰余が射影的な平坦加群は、完備化への普遍単射性から Mittag–Leffler 性を得る。
方針：完備化の Mittag–Leffler 性を、指定した標準写像の普遍単射性で降下する。
規約：KST §5、Stacks 05DP の降下部分。基礎環は完備な Noether 環。
使われ方：可算生成平坦 Mittag–Leffler 判定への入力。
-/
theorem isModuleMittagLeffler_of_adicCompletion_universally_injective
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) [IsAdicComplete I R]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (hinj : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective ((AdicCompletion.of I M).rTensor Q)) :
    IsModuleMittagLeffler R M :=
  isModuleMittagLeffler_of_universally_injective (AdicCompletion.of I M) hinj
    (isModuleMittagLeffler_adicCompletion_of_projective_reduction I)

/--
概要：完備な Noether 基底の有限型代数上の有限平坦加群は、射影的剰余とファイバー条件から射影的。
方針：05DM と 05DK から Mittag–Leffler 性を降下し、有限型の可算生成平坦加群の判定を使う。
規約：KST §5、Stacks 05DP, Lemma 38.9.1、ファイバー条件は実際の随伴素イデアルで量化する。
使われ方：05FS の射影性の存在の完備化側。
-/
theorem projective_of_complete_of_fibre_associatedPrimes
    (R S N : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] (I : Ideal R) [IsAdicComplete I R]
    [Module.Projective (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))]
    (hFib : ∀ (p : PrimeSpectrum R) (q : Ideal S),
      q.comap (algebraMap R S) = p.asIdeal →
      q ∈ associatedPrimes S (N ⊗[R] p.asIdeal.ResidueField) →
        I.map (algebraMap R S) ⊔ q ≠ ⊤) : Module.Projective R N := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply projective_of_finiteType_finite_flat_mittagLeffler R S N
  exact isModuleMittagLeffler_of_adicCompletion_universally_injective I
    (fun Q _ _ => adicCompletion_of_rTensor_injective_of_fibre_associatedPrimes I hFib Q)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
