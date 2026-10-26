module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ExtendedSourceSliceInput
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputCoconeNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexCoconeLift

/-!
概要：指定 compact 始点を含む全入力の余錐を元の under 図式の余錐に戻す。
方針：元の compact 始域 slice へ全余錐を持ち上げ、既存の反復 coslice 同型で戻す。
規約：元の全可変入力の余錐値を厳密に回収する。
使われ方：compact 成分射影の under comma の全余錐の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：指定始点を含む入力の compact な slice 余錐から元の under 図式の全余錐を得る。
方針：同じ全余錐を compact 始域 slice へ持ち上げ、反復 coslice の逆で戻す。
規約：元の可変図式の全余錐値を包含後も厳密に保つ。
使われ方：元の引き戻しの全余錐との厳密な成分合わせ。 -/
lemma exists_sourceUnderCocone_of_extendedInputCocone
    {A K : SSet.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (μ : Cardinal.{u}) (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ compactSourceSlice μ x}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceUnder z)
    (c : JoinCocone (extendedSourceSliceDiagram μ x t))
    (hc : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex)) :
    ∃ d : JoinCocone t,
      (mapJoinCocone (compactSourceSliceInclusion μ x)
        (mapJoinCocone (sliceUnderProjection z) d)).val =
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInr A K)) (𝟙 Δ[0]) ≫ c.val := by
  let P := fun v : (sliceOver x) _⦋0⦌ ↦
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v)
  let s := liftedUnderInputDiagram t
  let cy := fullSubcomplexCoconeLift P s c hc
  obtain ⟨d, hd⟩ := exists_liftedUnderCocone_of_inputCocone t cy
  have hcy : cy.val ≫ compactSourceSliceInclusion μ x = c.val := by
    exact fullSubcomplexLift_ι P c.val (fullSubcomplexCocone_vertices P s c hc)
  refine ⟨d, ?_⟩
  change (mapJoinCocone (sliceUnderProjection z) d).val ≫ compactSourceSliceInclusion μ x = _
  rw [hd, Category.assoc, hcy]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
