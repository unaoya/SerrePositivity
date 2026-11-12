module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalFaceIdentities

/-!
概要：最後の面からの一意な延長により頂点の終対象性を検出する。
方針：境界の最後の面を延ばし、他の面は共通部分と最後の頂点から一意に回収する。
規約：周囲の quasicategory 性を要求しない。
使われ方：任意の単体集合の右錐の右頂点の終対象性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 最後の面を、同じ最後の頂点を固定して一意に延長できれば終対象。 -/
lemma isTerminalVertex_of_unique_lastFace {X : SSet.{u}} (x : X _⦋0⦌)
    (hext : ∀ (n : ℕ) (g : (Δ[n] : SSet.{u}) ⟶ X),
      ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ X,
        stdSimplex.δ (Fin.last (n + 1)) ≫ f = g ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap (n + 1) ≫ f = SSet.yonedaEquiv.symm x)
    (huniq : ∀ (n : ℕ) (f g : (Δ[n + 1] : SSet.{u}) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap (n + 1) ≫ f = SSet.yonedaEquiv.symm x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap (n + 1) ≫ g = SSet.yonedaEquiv.symm x →
      stdSimplex.δ (Fin.last (n + 1)) ≫ f =
        stdSimplex.δ (Fin.last (n + 1)) ≫ g → f = g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n b hb
  obtain ⟨f, hf, hv⟩ := hext n (boundary.ι (Fin.last (n + 1)) ≫ b)
  refine ⟨f, ?_⟩
  apply boundary.hom_ext
  intro i
  change stdSimplex.δ i ≫ f = boundary.ι i ≫ b
  cases n with
  | zero =>
    fin_cases i
    · have hi : boundary.ι (0 : Fin 2) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex 0 (Fin.last 1) := by
        apply (cancel_mono (boundary 1).ι).mp
        rw [boundary.ι_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
        rw [stdSimplex.δ_zero_eq_const, SSet.yonedaEquiv_symm_zero]
        rfl
      have hz : stdSimplex.{u}.δ (0 : Fin 2) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap 1 := by
        change stdSimplex.map (SimplexCategory.δ 0) = stdSimplex.map _
        rw [SimplexCategory.δ_zero_eq_const]
        rfl
      change stdSimplex.δ (0 : Fin 2) ≫ f = boundary.ι (0 : Fin 2) ≫ b
      rw [hz, hv, hi, hb]
    · exact hf
  | succ n =>
    induction i using Fin.lastCases with
    | last => exact hf
    | cast i =>
      apply huniq n
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap_face]
        exact hv
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap_boundaryFace]
        exact hb
      · have hδ : stdSimplex.{u}.δ (Fin.last (n + 1)) ≫ stdSimplex.δ i.castSucc =
            stdSimplex.δ i ≫ stdSimplex.δ (Fin.last (n + 2)) := by
          have h := congrArg (fun a => stdSimplex.{u}.map a)
            (SimplexCategory.δ_comp_δ (i := i) (j := Fin.last (n + 1))
              (Fin.le_last i)).symm
          simpa only [CategoryTheory.Functor.map_comp, CosimplicialObject.δ,
            Fin.succ_last] using h
        rw [← Category.assoc, hδ, Category.assoc, hf]
        exact congrArg (fun a => a ≫ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.boundaryLastFace_comp n i).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
