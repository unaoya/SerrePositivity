module

public import SerrePositivity.Paper.Section5.ModuleReduction
public import SerrePositivity.Paper.Section2.Lemma2_1
public import SerrePositivity.IntersectionMultiplicity.BaseChange

/-! # 完備な場合の剰余体拡大による帰着

Lemma 2.1 で剰余体を代数閉体へ拡大する。環・加群の次元と交点重複度の保存は
平坦局所拡大の一般論から供給する。剰余体の代数閉性を外した完備・正剰余標数の場合を得る。
完備化による帰着は `CompletionReduction.lean` で扱い、剰余標数零の場合は残る。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 完備正則局所環で剰余標数が正なら、任意の有限生成加群に対して正値性が成り立つ。
剰余体は代数閉でなくてよい。Lemma 2.1 と核心定理の既存の引用入力に依存する。 -/
theorem positivity_of_complete_residueCharP
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  obtain ⟨S, sRing, sLocal, sNoetherian, sComplete, rsAlg, rsLocal,
      hflat, hm, ⟨ek, _⟩, _, hregular, _⟩ := Section2.lemma_2_1 R
  let := hflat
  let : IsRegularLocalRing S := hregular inferInstance
  let : IsAlgClosed (ResidueField S) := IsAlgClosed.of_ringEquiv _ _ ek.symm
  let : CharP (ResidueField S) p := charP_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _) p
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply positivity_of_complete_algClosed S p (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity.Section5
