module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyComparison

/-!
概要：実層の一次ホモロジー作用素の cycle は、正単体次元では境界である。
方針：総次数を固定した自然な層同型で、非退化 H(G) bar の完全性へ移す。
規約：連結射は全 HA 成分を持つ実段階の短完全列から作る。
使われ方：有限 support を持つホモロジー類の最大単体次元を下げる。
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

lemma dgCoherentBarLayerHomology_cycle_boundary (x : D) (n : ℕ) (q : ℤ)
    (b : ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1))).homology q)
    (hb : (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x n) (q + 1))
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ q (q + 1) (by simp) b) = 0) :
    ∃ c : ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 2))).homology (q - 1),
      (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) q)
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ (q - 1) q
          (by change q - 1 + 1 = q; omega) c) = b := by
  let r : ℤ := q + (n + 1 : ℕ)
  let B := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r)
  let e₀ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x n (q + 1) r (by dsimp [r]; omega)
  let e₁ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x (n + 1) q r (by dsimp [r]; omega)
  let e₂ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x (n + 2) (q - 1) r (by dsimp [r]; omega)
  have h₀ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarConnectingHomology_comparison R D G x n q (q + 1) r
    rfl (by dsimp [r]; omega) (by dsimp [r]; omega)
  have h₁ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarConnectingHomology_comparison R D G x (n + 1) (q - 1) q r
    (by omega) (by dsimp [r]; omega) (by dsimp [r]; omega)
  have hb' : B.d (n + 1) n (e₁.hom b) = 0 := by
    have h := ConcreteCategory.congr_hom h₀ b
    change e₀.hom ((HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x n) (q + 1))
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ q (q + 1) (by simp) b)) =
        B.d (n + 1) n (e₁.hom b) at h
    rw [hb, map_zero] at h
    exact h.symm
  have he := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondeg_exactAt R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) n
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at he
  obtain ⟨c, hc⟩ := he (e₁.hom b) hb'
  refine ⟨e₂.inv c, ?_⟩
  apply (ModuleCat.mono_iff_injective e₁.hom).mp inferInstance
  have h := ConcreteCategory.congr_hom h₁ (e₂.inv c)
  have hi : e₂.hom (e₂.inv c) = c := by
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  change e₁.hom ((HomologicalComplex.homologyMap
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) q)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ (q - 1) q
      (by change q - 1 + 1 = q; omega) (e₂.inv c))) =
        B.d (n + 2) (n + 1) (e₂.hom (e₂.inv c)) at h
  rw [hi] at h
  exact h.trans hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
