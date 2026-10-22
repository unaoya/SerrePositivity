module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.StrictClassifiedIndCocone

/-!
概要：元の weighted 密度余錐と strict 分類標準余錐は、Indκ 内で同じ指定頂点を持つ。
方針：両全余錐を全部分包含へ戻して元の同じ全空間余極限の分類値を計算する。
規約：頂点の同型でなく厳密な等号。使われ方：二重余極限の比較の終点の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

/-- 同じ strict 標準分類余錐と元の weighted 密度余錐の頂点は、Indκ 内で厳密に等しい。 -/
lemma weightedIndDensityCocone_vertex_eq_standard
    (hF : ∀ v, IsIndVertex κ C
      ((strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌) v)) :
    (weightedIndDensityCocone κ F).vertex = (strictClassifiedIndCocone κ F hF).vertex := by
  have hc : (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      (strictClassifiedIndCocone κ F hF).vertex = (strictRightStraighteningCocone F).vertex := by
    have h := congrArg (fun f => SSet.yonedaEquiv (joinInr _ Δ[0] ≫ f))
      (strictClassifiedIndCocone_inclusion_val κ F hF)
    rw [← Category.assoc, SSet.yonedaEquiv_comp,
      ← JoinCocone.vertex_eq, ← JoinCocone.vertex_eq] at h
    exact h
  apply Subtype.ext
  exact (weightedIndDensityCocone_vertex κ F).trans
    ((rightStraighteningPresheafDiagram_vertex (strictRightFibrationColimit F)).trans
      (hc.trans (strictRightStraighteningCocone_vertex F)).symm)

end SerrePositivity.InfinityCategories.F2.Ind
