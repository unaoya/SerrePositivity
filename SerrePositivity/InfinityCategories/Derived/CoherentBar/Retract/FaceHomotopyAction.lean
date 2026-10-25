module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFaceTerms
/-!
概要：面列の後の正規化ホモトピーを、面の単体上の退化列へ制限する。
方針：面の直和包含への制限で判定し、面の次数が段階より低ければ零とする。
規約：元の面ブロック・単体ラベルと全 Hom を保持する。
使われ方：正規化境界の面項の比較、および最後の正規化段の次数消滅。
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

lemma dgCoherentBarFaceRightTerm_zero {n : ℕ} (s : I _⦋n + 1⦌)
    (q : ℕ) (hq : n < q) (i : Fin (n + 1)) :
    dgCoherentBarFaceRightTerm R D F s q i = 0 := by
  unfold dgCoherentBarFaceRightTerm dgCoherentBarFaceColumn
  rw [moduleHomClosedInsertion R D,
    dgCoherentBarNormalizationHomotopyGraded_restrict,
    dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q
      (dgCoherentBarFace s i.succ) hq, DGNerve.zero_compose]

lemma dgCoherentBarFaceRightTerm_action {n : ℕ} (s : I _⦋n + 1⦌)
    (q : ℕ) (hq : q ≤ n) (i : Fin (n + 1)) :
    dgCoherentBarFaceRightTerm R D F s q i =
    ((q : ℤ) + 1).negOnePow • compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarFace s i.succ)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarDegeneracyColumn R D F (dgCoherentBarFace s i.succ).2
        ⟨n - q, by change n - q < n + 1; omega⟩)
      (dgCoherentBarFaceBlock R D F s i) rfl := by
  unfold dgCoherentBarFaceRightTerm dgCoherentBarFaceColumn
  rw [moduleHomClosedInsertion R D, dgCoherentBarNormalizationHomotopyGraded_restrict]
  unfold dgCoherentBarNormalizationHomotopyColumn
  rw [ite_eq_right (by change ¬n < q; omega), compose_units_smul_left]
  rfl

end SerrePositivity.InfinityCategories
