module

public import SerrePositivity.PerfectComplex.NormalizedLength

/-! # 正の長さをもつ加群の係数環は非自明

長さ代数の存在定理が返す環について、非自明性を長さの公式から確認する。
-/

@[expose] public section

universe u

namespace SerrePositivity.NormalizedLength

/-- 正の長さをもつ加群が存在すれば、係数環は非自明である。 -/
lemma nontrivial_ring_of_len_pos
    {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
    (M : Type u) [AddCommGroup M] [Module C M] (hM : 0 < lam.len M) : Nontrivial C := by
  by_contra hC
  have : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
  have : Subsingleton M := Module.subsingleton C M
  exact hM.ne' (lam.len_eq_zero_of_subsingleton M)

end SerrePositivity.NormalizedLength
