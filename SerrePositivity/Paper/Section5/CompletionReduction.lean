module

public import SerrePositivity.Paper.Section5.ResidueFieldReduction
public import SerrePositivity.CommutativeAlgebra.AdicCompletionNoetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # 完備化による帰着

Noether 性を供給した完備化に平坦局所拡大の保存則を適用する。
正の剰余標数の任意の正則局所環で、有限生成加群の交点重複度の正値性を得る。
§2・§4 と既存の交点理論などの引用入力への依存は残り、剰余標数零は扱わない。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 正の剰余標数の正則局所環で正値性が成り立つ。
完備化で有限長・次元・正則性・χを保存し、完備な場合に帰着する。
新しい未証明入力はなく、核心定理などの既存の引用入力に依存する。 -/
theorem positivity_of_residueCharP
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    AdicCompletion.maximalIdeal_eq_map.symm
  let : IsRegularLocalRing S := isRegularLocalRing_of_flat_of_map_maximalIdeal R S hm
  let : CharP (ResidueField S) p := charP_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _) p
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply positivity_of_complete_residueCharP S p (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity.Section5
