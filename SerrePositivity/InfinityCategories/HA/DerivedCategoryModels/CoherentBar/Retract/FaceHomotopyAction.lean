module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryFaceTerms
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarFaceRightTerm_zero {n : ℕ} (s : I _⦋n + 1⦌)
    (q : ℕ) (hq : n < q) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm R D F s q i = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomClosedInsertion R D,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded_restrict,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ) hq, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]

lemma dgCoherentBarFaceRightTerm_action {n : ℕ} (s : I _⦋n + 1⦌)
    (q : ℕ) (hq : q ≤ n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm R D F s q i =
    ((q : ℤ) + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyColumn R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ).2
        ⟨n - q, by change n - q < n + 1; omega⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i) rfl := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn
  rw [moduleHomClosedInsertion R D, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded_restrict]
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyColumn
  rw [ite_eq_right (by change ¬n < q; omega), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
