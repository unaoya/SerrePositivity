module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomPrecomp
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionTotalPrecomposition
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeSectionInitialComparison

/-!
概要：普遍前置の始点を、元の制限比較の同じ終点族と相対切断の像へ厳密に同定する。
方針：初期 Hom のパラメータ自然性と元の initialRestrictionEdgeFamily の定義を使う。
規約：選択の自然性は仮定しない。使われ方：元の HL・HR の lift への比較の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "a" => initialRestrictionEdgeFamily p q r hr d hd e y

/-- 普遍前置の始点は、元の同じ制限辺の族に相対切断を続けた初期 Hom 族である。 -/
lemma initialRestrictionSection_source :
    leftFibrationInitialSection p d hd y ≫ initialRestrictionTotalPrecomposition p q r hr d e y =
      initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm e) y (a ≫ relativeEdgeCosliceSection t q)
        (initialHomEdgeSectionInput_fixed q t y a
          (initialRestrictionEdgeFamily_fixed p q r hr d hd e y)) := by
  rw [initialRestrictionTotalPrecomposition,
    ← Category.assoc (leftFibrationInitialSection p d hd y), initialTotalEdgePrecomposition,
    initialDiagramHomFamily_precomp]
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
  rw [initialDiagramHomFamily, vertexFiberLift_ι, initialDiagramHomFamily, vertexFiberLift_ι]
  simp only [initialTotalEdgeFamily, initialRestrictionEdgeFamily, Category.assoc]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
