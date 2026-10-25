module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixVanishing
/-!
概要：正規化ホモトピーを prefix 列に合成すると、切断後の退化列になる。
方針：余積包含を通る Hom 合成を、元の tail のホモトピー列へ制限する。
規約：切断後の単体次数と全斉次作用を保持し、無限和は使わない。
使われ方：残存 prefix 項を前側の退化ブロック合成と比較する。
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

lemma dgCoherentBarHomotopy_comp_prefixColumn {n : ℕ} (s : I _⦋n⦌)
    (k q : ℕ) (hk : k + 1 ≤ n) (hq : q ≤ n - (k + 1)) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationHomotopyGraded R D F q)
      (dgCoherentBarPrefixColumn R D F s k hk) (show (1 : ℤ) + -1 = 0 from rfl) =
    ((q : ℤ) + 1).negOnePow • compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s (k + 1) hk)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarDegeneracyColumn R D F (dgCoherentBarTail s (k + 1) hk).2
        ⟨n - (k + 1) - q, by
          change n - (k + 1) - q < n - (k + 1) + 1
          omega⟩)
      (dgCoherentBarPrefixBlock R D F s k hk) (show (1 : ℤ) + -1 = 0 from rfl) := by
  unfold dgCoherentBarPrefixColumn
  rw [moduleHomClosedInsertion R D, dgCoherentBarNormalizationHomotopyGraded_restrict]
  unfold dgCoherentBarNormalizationHomotopyColumn
  rw [ite_eq_right (by change ¬n - (k + 1) < q; omega), compose_units_smul_left]
  rfl

end SerrePositivity.InfinityCategories
