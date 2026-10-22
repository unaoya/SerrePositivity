module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftSectionBifunctor
public import SerrePositivity.InfinityCategories.F1.KanDiagramRealization

/-!
概要：元の通常の添字と全相対定義域の同時評価を、同じ積図式の coherent 表示へ同定する。
方針：全ての順序 path で、後合成と前合成の元の混合作用を計算する。
規約：全次数の等式であり、頂点だけの一致ではない。
使われ方：strict 分類像の実現と全単体切断図式の実現の大域比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I J L : Type u} [Category.{u} I] [Category.{u} J] [LinearOrder L]
  {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B) (A : Jᵒᵖ ⥤ Over B)

/-- 同じ二つの順序図式の対角評価は、元の切断の積図式の coherent 表示そのもの。 -/
lemma sectionProductDiagonalRealization (Q : L ⥤ I) (R : L ⥤ J) :
    diagonalKanDiagramEvaluation R
      (enrichedFunctorOfOrderDiagram (Q ⋙ strictLeftSectionKanDiagramFamily F A)) =
    enrichedFunctorOfOrderDiagram (Q.prod' R ⋙ strictLeftSectionProductDiagram F A) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalKanDiagramHom R
    (enrichedFunctorOfOrderDiagram (Q ⋙ strictLeftSectionKanDiagramFamily F A)) i j).app n P = _
  rw [diagonalKanDiagramHom_of_le _ _ i j hij]
  change (strictDiagramMixedHom (R.map (homOfLE hij))
      (((strictLeftSectionKanDiagramFamily F A).obj (Q.obj i.as)).val ⋙ kanObjectForget)
      (((strictLeftSectionKanDiagramFamily F A).obj (Q.obj j.as)).val ⋙ kanObjectForget)).app n
    (PinchedHom.constant (SimplicialCategory.homEquiv' _ _
      ((strictLeftSectionKanDiagramFamily F A).map (Q.map (homOfLE hij)))) n.unop.len) = _
  rw [pinchedConstant_map]
  congr 1

end SerrePositivity.InfinityCategories.F2.Ind
