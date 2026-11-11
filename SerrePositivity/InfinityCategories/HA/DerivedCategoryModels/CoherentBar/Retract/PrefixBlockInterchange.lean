module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixRightComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixDegeneracyComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaceCoefficients
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
/-!
概要：重複頂点より前の prefix の二つの合成係数を異種等号で照合する。
方針：両側の係数を一つのシフトブロックに戻し、厳密な tail ラベル比較で直和包含を同定する。
規約：始域・終域と切断の全パラメーターを保持する。
使われ方：正規化境界の prefix 和を項ごとに相殺する。
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

lemma dgCoherentBarPrefixBlock_degeneracy_interchange_heq {n : ℕ} (s : I _⦋n⦌)
    (k q : ℕ) (hk : k + 1 ≤ n - q) :
    HEq (_root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ ⟨n - q, by omega⟩ s) (k + 1) (by omega))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F (I.σ ⟨n - q, by omega⟩ s) k (by omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩) rfl)
      (_root_.SerrePositivity.DifferentialGraded.compose R
      (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega))))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneracyAt q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega)))))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega)).2
        ⟨n - (k + 1) - q, by change n - (k + 1) - q < n - (k + 1) + 1; omega⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s k (by omega)) rfl) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩
  let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s (k + 1) (by omega))
  have hl := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPrefixBlock_degeneracy_before_comp R D F s
    ⟨n - q, by omega⟩ k hk
  have hr := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneracyBlock_prefix_before_comp R D F s k q (by omega)
  have hs := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractShiftBlock_heq R D M N M N rfl rfl
    (n : ℤ) ((n + 1 - (k + 1) : ℕ) : ℤ)
    (n : ℤ) ((n - (k + 1) + 1 : ℕ) : ℤ)
    rfl (by omega) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D F s k (by omega)) HEq.rfl
    (by omega : (n : ℤ) + -(k : ℤ) - ((n + 1 - (k + 1) : ℕ) : ℤ) = 0)
    (by omega : (n : ℤ) + -(k : ℤ) - ((n - (k + 1) + 1 : ℕ) : ℤ) = 0)
  exact hl.trans (hs.trans hr.symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
