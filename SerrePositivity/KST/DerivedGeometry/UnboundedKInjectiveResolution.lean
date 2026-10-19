module

public import SerrePositivity.KST.DerivedGeometry.SmallAcyclicTestCriterion
public import SerrePositivity.KST.DerivedGeometry.GrothendieckInjectiveTestFamily

/-!
概要：Grothendieck アーベル圏の任意の非有界複体に、各項 injective な K-injective 分解が存在する。
方針：実際に構成した小さい非輪状試験族と二項試験に small object argument を適用する。
規約：分解・K-injectivity の存在は結論として証明し、未証明フィールドや公理にはしない。
使われ方：Stacks Theorem 19.12.6 (079P)、TT §3・§8、Toën §3.2 の非有界導来関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：任意の非有界複体から各項 injective な K-injective 複体への単射準同型が存在する。
方針：小さい試験族の直交対象への構成に、証明済みの試験集合判定を適用する。
規約：有界性・対象の projectivity・完全な無限積を仮定しない。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の非有界 Dqc アフィン導来比較。
-/
lemma exists_unbounded_kInjective_resolution (M : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (j : M ⟶ I), Mono j ∧ QuasiIso j ∧
      I.IsKInjective ∧ ∀ n : ℤ, Injective (I.X n) := by
  let G := separator C
  obtain ⟨I, j, hj, hqj, hInj, hTest⟩ := exists_mono_quasiIso_injective_test_orthogonal
    (smallAcyclicTestFamily G) (fun s => s.prop.1) M
  have : ∀ n, Injective (I.X n) := hInj
  exact ⟨I, j, hj, hqj, isKInjective_of_smallAcyclicTests G (isSeparator_separator C) I hTest, hInj⟩

end SerrePositivity.KST.DerivedGeometry
