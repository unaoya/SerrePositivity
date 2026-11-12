module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageHomologyDescent

/-!
概要：隣接二段の包含で消える低い段階からの類は、一段目ですでに消える。
方針：長完全列の連結射の代表を一次完全性で置き換え、連続する連結射を零にする。
規約：全 HA 成分を持つ実段階とその長完全列を使う。
使われ方：零段階からの核が最初の一次境界だけで生成されることの証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarStageHomology_kernel_descent (x : D) (p : ℤ) (n : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).homology (p + 1))
    (ha : HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (show n ≤ n + 2 by omega)) (p + 1) a = 0) :
    HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n)) (p + 1) a = 0 := by
  let i := HomologicalComplex.homologyMap
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n)) (p + 1)
  let j := HomologicalComplex.homologyMap
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ (n + 1))) (p + 1)
  have hja : j (i a) = 0 := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageMap_comp]
    exact ha
  let Δ : ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 2))).homology p ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x (n + 1)).homology (p + 1) :=
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ p (p + 1) (by simp)
  have he : ∀ z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x (n + 1)).homology (p + 1),
      j z = 0 → ∃ b : ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 2))).homology p, Δ b = z := by
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).homology_exact₁
        p (p + 1) (by simp))
  obtain ⟨b, hb⟩ := he (i a) hja
  have hPa : HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) (p + 1) (i a) = 0 := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageMap_toLayer_zero, HomologicalComplex.homologyMap_zero]
    rfl
  have hbcycle : HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) (p + 1)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ
        p (p + 1) (by simp) b) = 0 := by
    exact (congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x (n + 1)).homology (p + 1) => HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) (p + 1) z) hb).trans hPa
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomology_cycle_boundary R D G x (n + 1) p b hbcycle
  have hz := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).comp_δ p (p + 1)
      (by simp))
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 2)).δ
        (p - 1) p (by change p - 1 + 1 = p; omega) c)
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ p (p + 1)
    (by simp)
    (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 2)) p
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 2)).δ
        (p - 1) p (by change p - 1 + 1 = p; omega) c)) = 0 at hz
  rw [hc] at hz
  exact hb.symm.trans hz

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
