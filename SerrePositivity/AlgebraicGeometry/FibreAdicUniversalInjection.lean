module

public import SerrePositivity.AlgebraicGeometry.TensorFibreAssociatedPrimes
public import SerrePositivity.AlgebraicGeometry.AdicCompletionUniversalInjection

/-!
概要：KST §5、Stacks 05DM, Lemma 38.8.4 のファイバー条件による完備化への普遍単射性。
方針：ファイバーの随伴素イデアルの条件を全有限テンソル試験へ移し、普遍単射性の判定を使う。
規約：元の環と作用する環の双方が Noether、加群は後者上有限かつ前者上平坦。
使われ方：Stacks 05DP の射影性の存在。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：各ファイバーの随伴素イデアルが中心と互いに素でなければ、完備化への標準写像は普遍単射。
方針：随伴素イデアルのファイバーへの包含と、有限試験から任意の試験への単射性を接続する。
規約：KST §5、Stacks 05DM, Lemma 38.8.4、ファイバーは縮約素イデアルで指定する。
使われ方：完備化の Mittag–Leffler 性を元の加群へ降下する。
-/
theorem adicCompletion_of_rTensor_injective_of_fibre_associatedPrimes
    {R S N : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] (I : Ideal R)
    (hFib : ∀ (p : PrimeSpectrum R) (q : Ideal S),
      q.comap (algebraMap R S) = p.asIdeal →
      q ∈ associatedPrimes S (N ⊗[R] p.asIdeal.ResidueField) →
        I.map (algebraMap R S) ⊔ q ≠ ⊤)
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((AdicCompletion.of I N).rTensor Q) := by
  apply adicCompletion_of_rTensor_injective_of_associatedPrimes_tests
    (R := R) (S := S) (N := N) I ?_ Q
  intro P hP hRP hfin
  exact associatedPrimes_tensorProduct_subset_of_fibres
    {q | I.map (algebraMap R S) ⊔ q ≠ ⊤} hFib P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
