module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorAssociatedPrimeDevissage
public import SerrePositivity.AlgebraicGeometry.FibreAssociatedPrimeContraction

/-!
概要：KST §5、Stacks 05C2 の有限加群との平坦テンソルの随伴素イデアルのファイバーへの包含。
方針：素剰余による帰着を、素剰余から剰余体への平坦テンソル単射で接続する。
規約：包含側だけを使い、随伴素イデアルの等式全体は主張しない。
使われ方：Stacks 05DM の元のファイバー条件から有限テンソル試験の条件を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：有限加群との平坦テンソルの随伴素イデアルは、縮約素イデアルでのファイバーの条件で制御できる。
方針：素イデアル剰余から剰余体への単射をテンソルし、随伴素イデアルの縮約を特定する。
規約：KST §5、Stacks 05C2, Lemma 10.65.5 の包含側。両環を Noether とする。
使われ方：ファイバーの随伴素イデアルの条件を各有限テンソルに移す。
-/
theorem associatedPrimes_tensorProduct_subset_of_fibres
    {R S N : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Flat R N]
    (U : Set (Ideal S))
    (hU : ∀ (p : PrimeSpectrum R) (q : Ideal S),
      q.comap (algebraMap R S) = p.asIdeal →
      q ∈ associatedPrimes S (N ⊗[R] p.asIdeal.ResidueField) → q ∈ U)
    (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Finite R Q] :
    associatedPrimes S (N ⊗[R] Q) ⊆ U := by
  apply associatedPrimes_tensorProduct_subset_of_prime_quotients U ?_ Q
  intro p hp
  let := hp
  intro q hq
  let j : (R ⧸ p) →ₗ[R] p.ResidueField :=
    (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap
  let J := TensorProduct.AlgebraTensorModule.lTensor S N j
  have hJ : Function.Injective J :=
    Module.Flat.lTensor_preserves_injective_linearMap j
      p.injective_algebraMap_quotient_residueField
  have hfibre := hq.map_of_injective J hJ
  exact hU ⟨p, hp⟩ q (associatedPrime_tensor_residueField_comap p q hfibre) hfibre

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
