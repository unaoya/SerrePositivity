module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixTermInterchange
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixHomotopyAction
/-!
概要：正の退化位置で正規化境界の二つの prefix 有限和が相殺する。
方針：前側の切断は全 Hom の交換式、後側の切断は係数消滅で照合し、次元符号を相殺する。
規約：元の theta の全 prefix を含め、通常の辺合成への置換をしない。
使われ方：正規化境界を始点保存の面・退化作用だけの式に還元する。
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

abbrev dgCoherentBarPrefixLeftTerm {n : ℕ} (s : I _⦋n⦌) (q : ℕ) (k : Fin (n + 1)) :
    GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) 0 :=
  _root_.SerrePositivity.DifferentialGraded.compose R
    (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F (I.σ ⟨n - q, by omega⟩ s) k.val (by omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩)
    (show (-1 : ℤ) + 1 = 0 from rfl)

abbrev dgCoherentBarPrefixRightTerm {n : ℕ} (s : I _⦋n⦌) (q : ℕ) (k : Fin n) :
    GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) 0 :=
  _root_.SerrePositivity.DifferentialGraded.compose R
    (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationHomotopyGraded R D F q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F s k.val (by omega))
    (show (1 : ℤ) + -1 = 0 from rfl)

lemma dgCoherentBarPrefixRightTerm_eq_signed_left {n : ℕ} (s : I _⦋n⦌)
    (q : ℕ) (hq : q < n) (k : Fin n) :
    dgCoherentBarPrefixRightTerm R D F s q k =
      ((q : ℤ) + 1).negOnePow • dgCoherentBarPrefixLeftTerm R D F s q k.castSucc := by
  by_cases hk : k.val + 1 ≤ n - q
  · have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarHomotopy_comp_prefixColumn R D F s k.val q (by omega)
      (by omega)
    exact h.trans (congrArg (fun z => ((q : ℤ) + 1).negOnePow • z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixColumn_degeneracy_interchange R D F s k.val q hk).symm)
  · have hr := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarHomotopy_comp_prefixColumn_zero R D F s k.val q
      (by omega) (by omega)
    have hl := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneratePrefix_comp_block_zero R D F s
      ⟨n - q, by omega⟩ k.val (by omega) (by omega)
      (by change n - q ≤ k.val; omega)
    have hl' : dgCoherentBarPrefixLeftTerm R D F s q k.castSucc = 0 := hl
    exact hr.trans ((congrArg (fun z => ((q : ℤ) + 1).negOnePow • z) hl').trans
      (smul_zero _)).symm

lemma dgCoherentBarPrefixLeftTerm_last {n : ℕ} (s : I _⦋n⦌)
    (q : ℕ) (hq : q < n) :
    dgCoherentBarPrefixLeftTerm R D F s q (Fin.last n) = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneratePrefix_comp_block_zero R D F s
    ⟨n - q, by omega⟩ n (by omega) (by omega) (by omega)

lemma dgCoherentBarPrefixRightSum_eq_signed_left {n : ℕ} (s : I _⦋n⦌)
    (q : ℕ) (hq : q < n) :
    (∑ k : Fin n, dgCoherentBarPrefixRightTerm R D F s q k) =
      ((q : ℤ) + 1).negOnePow •
        ∑ k : Fin (n + 1), dgCoherentBarPrefixLeftTerm R D F s q k := by
  have hs : (∑ k : Fin (n + 1), dgCoherentBarPrefixLeftTerm R D F s q k) =
      ∑ k : Fin n, dgCoherentBarPrefixLeftTerm R D F s q k.castSucc := by
    rw [Fin.sum_univ_castSucc, dgCoherentBarPrefixLeftTerm_last R D F s q hq, add_zero]
  rw [hs, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact dgCoherentBarPrefixRightTerm_eq_signed_left R D F s q hq k

lemma dgCoherentBarNormalizationPrefixSums_cancel {n : ℕ} (s : I _⦋n⦌)
    (q : ℕ) (hq : q < n) :
    ((q : ℤ) + 1).negOnePow • (((n : ℤ) + 1).negOnePow •
      ∑ k : Fin (n + 1), dgCoherentBarPrefixLeftTerm R D F s q k) +
    (n : ℤ).negOnePow • (∑ k : Fin n, dgCoherentBarPrefixRightTerm R D F s q k) = 0 := by
  rw [dgCoherentBarPrefixRightSum_eq_signed_left R D F s q hq]
  rw [smul_comm (n : ℤ).negOnePow (((q : ℤ) + 1).negOnePow), ← smul_add]
  have hn : ((n : ℤ) + 1).negOnePow = -(n : ℤ).negOnePow := by
    rw [Int.negOnePow_add]
    simp
  rw [hn]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul, neg_add_cancel, zsmul_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
