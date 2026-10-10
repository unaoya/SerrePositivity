module

public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.CommutativeAlgebra.FlatLocalDimension

/-! # 平坦局所拡大による交点重複度の保存

極大イデアルを保つ平坦局所拡大で、テンソル積の長さ、各 Tor の長さ、交点重複度が保存される。
有限長性や正則性を仮定せず、長さの無限値も含めた公式を示す。
-/

public section

universe u

namespace SerrePositivity

open IsLocalRing TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

include hm in
/-- 平坦局所拡大は両変数を係数拡大したテンソル積の長さを保つ。 -/
theorem tensorLength_baseChange_of_map_maximalIdeal :
    Module.length B ((B ⊗[A] M) ⊗[B] (B ⊗[A] N)) = Module.length A (M ⊗[A] N) := by
  rw [← (AlgebraTensorModule.distribBaseChange A B M N).length_eq]
  exact length_baseChange_of_map_maximalIdeal A B hm _

include hm in
/-- 平坦局所拡大はすべての次数で Tor の長さを保つ。 -/
theorem torLength_baseChange_of_map_maximalIdeal (i : ℕ) :
    torLength B i (B ⊗[A] M) (B ⊗[A] N) = torLength A i M N := by
  unfold torLength
  rw [(torBaseChangeEquiv A B i M N).length_eq]
  exact length_baseChange_of_map_maximalIdeal A B hm _

include hm in
/-- 平坦局所拡大は交点重複度を保つ。 -/
theorem chi_baseChange_of_map_maximalIdeal :
    chi B (B ⊗[A] M) (B ⊗[A] N) = chi A M N := by
  unfold chi
  apply finsum_congr
  intro i
  rw [torLength_baseChange_of_map_maximalIdeal A B hm M N i]

end SerrePositivity
