module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentFilteredTotalDetection

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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion

/-- 全空間の各連結成分は、一つの元の値の連結成分の像である。 -/
lemma total_piZero_value_representative {B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (a : π₀ (coherentDiagramTotalKan F)) :
    ∃ b : B _⦋0⦌,
      ∃ t : π₀ (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj,
        mapπ₀ (coherentDiagramValueToTotalKan F b) t = a := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  obtain ⟨b, g, ⟨H⟩⟩ := coherentFilteredTotalKan_finite_value_detection F
    (SSet.const x : (Δ[0] : SSet.{u}) ⟶ _)
  let q := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  refine ⟨b, π₀.mk (g.app _ q), ?_⟩
  have h := mapPiZero_eq_of_homotopy H (π₀.mk q)
  simpa [SSet.const] using h.symm

end SerrePositivity.InfinityCategories.F2.PiCriterion
