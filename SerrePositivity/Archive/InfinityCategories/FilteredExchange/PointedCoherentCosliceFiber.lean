module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedCoherentCosliceNormalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedCoherentFiberComparison

/-!
概要：coherent な一点 coslice の全空間の正規化と、元の fiber 比較を照合する。
方針：表示変更の全単体の錐を読み、同じ fiber の包含との可換性を示す。
規約：元の係数と実射を保持。使われ方：全 pointed 族の始点の厳密な同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ一点の表示変更は、fiber と全 coslice の包含で厳密に可換する。 -/
lemma pointedCoherentCosliceIso_fiber (K : KanObject.{u}) :
    (pointedCoherentFiberIso K).hom ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex K) =
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm
      (coherentNerveVertex pointKanObject))) (coherentNerveVertex K) ≫
        pointedCoherentCosliceIso.hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact (cosliceFiberVerticesIso_app_val
    (spaceInfinityVertex_eq_coherent pointKanObject).symm rfl n a).trans
      (pointedCoherentCosliceIso_app_val a.val).symm

/-- 全反転 Hom の標準 fiber 比較を、全 coslice の正規化と同じ射として読む。 -/
lemma pointedCoherentCosliceIso_comparison (K : KanObject.{u}) :
    pointedCoherentFiberComparison K ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex K) =
    coherentCosliceFiberComparison pointKanObject K ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveVertex K) ≫
          pointedCoherentCosliceIso.hom := by
  rw [pointedCoherentFiberComparison, Category.assoc, pointedCoherentCosliceIso_fiber]

end SerrePositivity.InfinityCategories.F2
