module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput

/-!
概要：D の元ごとの零次数条件を、全空間比較射の π₀ の全単射性へ渡す。
方針：全空間の値からの代表、元の脚との可換性、後続段階での同一視を合成する。
規約：D の公開構造を直接消費し、同じ構造を再定義しない。
使われ方：DGBarCompactFilteredSpacePiBridge の零次数の証明。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 元の値からの比較が零次数で可換なら、D の二つの零次数条件が π₀ 同型を与える。 -/
lemma bridge_mapPiZero_bijective {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ (i : I) (y : (X i).obj _⦋0⦌),
      π₀.mk (q.app _ ((s i).app _ y)) = π₀.mk ((l i).app _ y))
    (hstage : ∀ (i j : I) (hij : i ≤ j) (y : (X i).obj _⦋0⦌),
      π₀.mk ((s j).app _ ((τ hij).app _ y)) = π₀.mk ((s i).app _ y))
    (hrep : ∀ t : T.obj _⦋0⦌, ∃ (i : I) (y : (X i).obj _⦋0⦌),
      π₀.mk ((s i).app _ y) = π₀.mk t) :
    Function.Bijective (mapπ₀ q) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := π₀.mk_surjective b
    obtain ⟨i, xi, hxi⟩ := hrep x
    obtain ⟨j, yj, hyj⟩ := hrep y
    have hi := congrArg (mapπ₀ q) hxi
    have hj := congrArg (mapπ₀ q) hyj
    simp only [mapπ₀_mk] at hi hj hab
    have he : π₀.mk ((l i).app _ xi) = π₀.mk ((l j).app _ yj) :=
      (hcomm i xi).symm.trans (hi.trans (hab.trans (hj.symm.trans (hcomm j yj))))
    obtain ⟨k, hik, hjk, hk⟩ := h.components_equal_at_stage i j xi yj he
    have hs := congrArg (mapπ₀ (s k)) hk
    simp only [mapπ₀_mk] at hs
    exact hxi.symm.trans ((hstage i k hik xi).symm.trans
      (hs.trans ((hstage j k hjk yj).trans hyj)))
  · intro a
    obtain ⟨z, rfl⟩ := π₀.mk_surjective a
    obtain ⟨i, y, hy⟩ := h.components_surjective z
    refine ⟨π₀.mk ((s i).app _ y), ?_⟩
    exact (hcomm i y).trans hy

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
