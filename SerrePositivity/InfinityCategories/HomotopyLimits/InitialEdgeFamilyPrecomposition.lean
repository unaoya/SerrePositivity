module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialEdgeFamilyRetraction
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialTotalEdgePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomPrecomp

/-!
概要：元の全辺族の終端初期 Hom に普遍前置を作用させ、同じ終端族の相対切断へ同定する。
方針：終端の正規化表示を包含後に相殺し、パラメータ前合成自然性を使う。
規約：実際の辺と全族を保持。使われ方：枝終点の前置像を根辺の付加辺面と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  {c d : E _⦋0⦌} (e : E.Edge c d) (y : B _⦋0⦌)
  (a : T ⟶ sliceUnder (SSet.yonedaEquiv.symm e.edge))
  (ha : (a ≫ sliceUnderProjection (SSet.yonedaEquiv.symm e.edge)) ≫ q = SSet.const y)
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "J" => initialDiagramHomFamily q d t (stdSimplex.δ (0 : Fin 2))
  (SSet.Edge.δ_zero_yonedaEquiv_symm e) y a ha
local notation "K" => (a ≫ sliceUnderRestrict t (stdSimplex.δ (0 : Fin 2))) ≫
  relativeEdgeCosliceSection t q

/-- 終端の初期 Hom の前置像を包含すると、元の同じ終端族の普遍相対切断になる。 -/
lemma initialTotalEdgeFamily_terminal_initial : J ≫ initialTotalEdgeFamily q e y = K := by
  rw [initialTotalEdgeFamily, ← Category.assoc J
    (vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ q) y),
    initialDiagramHomFamily, vertexFiberLift_ι]
  simp only [normalizedCoconeRestriction, Category.assoc]
  rw [← Category.assoc (eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm)),
    eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]

/-- 終端初期 Hom の普遍前置は、同じ全辺族の相対切断を始点へ制限した族である。 -/
lemma initialTotalEdgePrecomposition_family : J ≫ initialTotalEdgePrecomposition q e y =
    initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
      (SSet.Edge.δ_one_yonedaEquiv_symm e) y K
      (initialEdgeFamilyRetraction_section_fixed q t y a ha) := by
  rw [initialTotalEdgePrecomposition, initialDiagramHomFamily_precomp]
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
  simp only [initialDiagramHomFamily, vertexFiberLift_ι]
  exact congrArg (· ≫ normalizedCoconeRestriction t (stdSimplex.δ (1 : Fin 2))
    (SSet.Edge.δ_one_yonedaEquiv_symm e)) (initialTotalEdgeFamily_terminal_initial q e y a ha)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
