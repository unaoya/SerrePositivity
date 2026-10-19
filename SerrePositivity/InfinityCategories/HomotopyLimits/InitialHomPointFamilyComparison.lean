module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber

/-!
概要：任意の点からの余錐の全パラメータ族を、始対象の Hom 比較と実際の辺の前合成で計算する。
方針：底の辺の終点切断で三角形の族を作り、相対充填と始対象の評価上のホモトピーを適用する。
規約：族の始点には始対象性を仮定しない。使われ方：貼った余錐の各枝の全 Hom の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) (c : E _⦋0⦌)
  (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q)) y)
  (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ vertexFiberι (sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q))) y)

/-- 全 Hom の底の族を、指定した比較辺を含む合成三角形の族へ延長する。 -/
def pointFamilyBaseTriangle : T ⟶ sliceUnder (e ≫ q) :=
  b ≫ cosliceEdgeSectionFiber (e ≫ q) y ≫ vertexFiberι (sliceUnderProjection (e ≫ q)) y

include h in
/-- 三角形の族の終点制限は元の全 Hom の底の族を厳密に回収する。 -/
lemma pointFamilyBaseTriangle_target :
    a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      pointFamilyBaseTriangle q e y b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)) := by
  simp only [pointFamilyBaseTriangle, Category.assoc, cosliceEdgeSectionFiber_ι,
    cosliceEdgeSection_target]
  erw [Category.comp_id]
  exact h

/-- 三角形の始点制限は、底の全 Hom の族と実際の辺の前合成の合成そのもの。 -/
lemma pointFamilyBaseTriangle_source :
    initialEdgeBaseSource q c e he y a ha (pointFamilyBaseTriangle q e y b)
        (pointFamilyBaseTriangle_target q e y a b h) =
      b ≫ cosliceEdgeFiberPrecomposition (e ≫ q) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q))
        (by rw [← Category.assoc, he]) rfl y := by
  apply vertexFiber_hom_ext
  rw [initialEdgeBaseSource, vertexFiberLift_ι, Category.assoc,
    cosliceEdgeFiberPrecomposition_ι]
  simp only [pointFamilyBaseTriangle, Category.assoc, cosliceEdgeSectionFiber_ι,
    cosliceEdgePrecompositionAt, cosliceEdgePrecomposition, normalizedCoconeRestriction,
    eqToHom_refl, Category.id_comp]

include he h in
/-- 始対象の Hom 比較は、任意の点からの族を、指定した比較辺の前合成で全単体において計算する。 -/
lemma initialHomComparison_pointFamily_homotopy [InnerFibration q] (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      (vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha ≫
        leftFibrationInitialHomComparison q c hc y)
      (b ≫ cosliceEdgeFiberPrecomposition (e ≫ q) (SSet.yonedaEquiv.symm c ≫ q)
        (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q))
        (by rw [← Category.assoc, he]) rfl y ≫ (leftFibrationInitialBaseIso q c y).hom)) := by
  have H := initialHomComparison_edge_family_pinched_homotopy q c e he y a ha
    (pointFamilyBaseTriangle q e y b) (pointFamilyBaseTriangle_target q e y a b h) hc
  rwa [pointFamilyBaseTriangle_source] at H

end
end SerrePositivity.InfinityCategories.HomotopyLimits
