module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryExpansion
/-!
概要：正の退化位置での実正規化境界は二つの符号付き面和だけで計算できる。
方針：元の境界の二つの合成を展開し、全 prefix 和の相殺を適用する。
規約：coherent な全高次作用を仮定で消さず、既証の相殺式で除く。
使われ方：正規化段階とラベル上の Dold–Kan 作用の比較。
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

private lemma cancel_prefix_summands {A : Type*} [AddCommGroup A]
    (a b c : ℤˣ) (f p g r : A) (h : a • (b • p) + c • r = 0) :
    a • (f + b • p) + (g + c • r) = a • f + g := by
  rw [smul_add]
  calc
    _ = (a • f + g) + (a • (b • p) + c • r) := by abel
    _ = _ := by rw [h, add_zero]

lemma dgCoherentBarNormalizationBoundary_restrict_faces {n : ℕ}
    (s : I _⦋n + 1⦌) (q : ℕ) (hq : q < n + 1) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n + 1, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded R D F q) =
    ((q : ℤ) + 1).negOnePow •
      (∑ i : Fin (n + 2), (((n + 1 : ℕ) : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s q i) +
    ∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm R D F s q i := by
  have hleft := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTheta_comp_homotopyColumn R D F s q (by omega)).trans
    (congrArg (fun z => ((q : ℤ) + 1).negOnePow • z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarColumn_degeneracy_comp_expansion R D F s q))
  have hright := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarHomotopy_comp_column_expansion R D F s q
  have htotal := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationBoundaryGraded_restrict R D F q ⟨n + 1, s⟩).trans
    (congrArg₂ (· + ·) hleft hright)
  have hcancel := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationPrefixSums_cancel R D F s q hq
  have hcancel' :
      ((q : ℤ) + 1).negOnePow •
        ((((n + 1 : ℕ) : ℤ) + 1).negOnePow •
          ∑ k : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixLeftTerm R D F s q k) +
      ((n : ℤ) + 1).negOnePow •
        (∑ k : Fin (n + 1), _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixRightTerm R D F s q k) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcancel
  exact htotal.trans (cancel_prefix_summands _ _ _ _ _ _ _ hcancel')

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
