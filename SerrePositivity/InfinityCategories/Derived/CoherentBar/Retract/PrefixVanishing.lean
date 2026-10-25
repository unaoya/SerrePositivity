module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FiltrationColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneratePrefixCoefficients
/-!
概要：正規化境界の prefix 和で、切断が退化位置を越えた項を消す。
方針：一方は退化高次係数の零性、他方は切断後の次数におけるホモトピー列の零性を使う。
規約：元の全 Hom 内の合成を計算し、評価ごとの零性だけで代用しない。
使われ方：残る prefix 項を重複頂点より前の切断だけに制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarHomotopy_comp_prefixColumn_zero {n : ℕ} (s : I _⦋n⦌)
    (k q : ℕ) (hk : k + 1 ≤ n) (hq : n - (k + 1) < q) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationHomotopyGraded R D F q)
      (dgCoherentBarPrefixColumn R D F s k hk) (show (1 : ℤ) + -1 = 0 from rfl) = 0 := by
  unfold dgCoherentBarPrefixColumn
  rw [moduleHomClosedInsertion R D,
    dgCoherentBarNormalizationHomotopyGraded_restrict,
    dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q
      (dgCoherentBarTail s (k + 1) hk) hq, DGNerve.zero_compose]

lemma dgCoherentBarDegeneratePrefix_comp_block_zero {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k + 1 ≤ n + 1)
    (hkpos : 1 ≤ k) (hj : j.val ≤ k) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarPrefixColumn R D F (I.σ j s) k hk)
      (dgCoherentBarDegeneracyBlock R D F s j) (show (-1 : ℤ) + 1 = 0 from rfl) = 0 := by
  unfold dgCoherentBarPrefixColumn
  rw [dgCoherentBarPrefixBlock_degenerate_zero R D F s j k hk hkpos (by omega),
    map_zero, DGNerve.zero_compose]

end SerrePositivity.InfinityCategories
