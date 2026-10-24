module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTensorCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorExtension

/-!
概要：元の実 Ind comma 内で試験族と下方余錐を同時に保つ全拡張を得る。
方針：補間領域の実余錐を、同じ形状同型の逆で元の余錐の積へ戻す。
規約：元の両全図式と共通境界を厳密に保持し、追加の充填仮定を課さない。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：一般の κ-small な両境界を同時に延長できる。
方針：実余錐を全形状へ戻す。規約：元の全射の等号。使われ方：点追加の全補間。 -/
lemma exists_indComma_coneTensor_extension (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A L : SSet.{u}} [Quasicategory C] (x : (IndInfinity κ C) _⦋0⦌)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ join L (Δ[0] : SSet.{u})) ⟶
      leftKanShape (indYoneda κ C) x)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ L) ⟶
      leftKanShape (indYoneda κ C) x)
    (h : (SSet.uliftFunctor.{u + 1, u}).map (A ◁ joinInl L (Δ[0] : SSet.{u})) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}) ▷ L) ≫ G) :
    ∃ E : (SSet.uliftFunctor.{u + 1, u}).obj
        (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) ⟶ leftKanShape (indYoneda κ C) x,
      (SSet.uliftFunctor.{u + 1, u}).map
        (joinInl A Δ[0] ▷ join L (Δ[0] : SSet.{u})) ≫ E = F ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ E = G := by
  obtain ⟨H, ⟨c⟩, hF, hG⟩ := exists_indComma_coneTensor_cocone κ x hA hL F G h
  let E := coneTensorExtend.{u, u + 1} c
  have he : (SSet.uliftFunctor.{u + 1, u}).map (coneTensorCornerInclusion A L) ≫ E = H :=
    coneTensorExtend_inclusion c
  refine ⟨E, ?_, ?_⟩
  · rw [← coneTensorCornerInclusion_old, Functor.map_comp, Category.assoc, he, hF]
  · rw [← coneTensorCornerInclusion_lower, Functor.map_comp, Category.assoc, he, hG]

end SerrePositivity.InfinityCategories.F2.Ind
