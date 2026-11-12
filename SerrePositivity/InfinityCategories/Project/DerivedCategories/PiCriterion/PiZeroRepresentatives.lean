module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection

/-!
概要：coherent filtered 全空間の各連結成分に、元の一つの値から代表を取る。
方針：零単体を有限な零次標準単体の射として検出し、実際のホモトピーを π₀ へ送る。
規約：非空性を仮定しない。空の全空間の成分には要求がない。
使われ方：filtered 余極限判定の零次数の元ごとの全射条件。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 全空間の各連結成分は、一つの元の値の連結成分の像である。 -/
lemma total_piZero_value_representative {B : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (a : π₀ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F)) :
    ∃ b : B _⦋0⦌,
      ∃ t : π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b) t = a := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  obtain ⟨b, g, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredTotalKan_finite_value_detection F
    (SSet.const x : (Δ[0] : SSet.{u}) ⟶ _)
  let q := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  refine ⟨b, π₀.mk (g.app _ q), ?_⟩
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_eq_of_homotopy H (π₀.mk q)
  simpa [SSet.const] using h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
