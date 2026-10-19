module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeNaturality

/-!
概要：底の比較辺を含む合成三角形の族から、固定終点の実際の Hom 比較の自然性を得る。
方針：持ち上げた族の射影を底の固定 fiber に戻し、始対象の評価上のホモトピーを後合成する。
規約：全パラメータにおける単体的ホモトピー。連結成分への作用だけではない。
使われ方：部分余極限の制限の正方形を、Hom の前合成による正方形へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}}
  (q : E ⟶ B) (c : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ sliceUnder (e ≫ q))
  (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)))

/-- 底の合成三角形の始点側を、指定した始点と固定終点の写像空間へ戻す。 -/
def initialEdgeBaseSource :
    T ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y :=
  vertexFiberLift _ y
    (b ≫ normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
      (by rw [← Category.assoc, he])) (by
        rw [Category.assoc, normalizedCoconeRestriction_projection,
          relativeEdgeCosliceFamily_projection e q a b h, ha])

/-- 始対象からの選ばれた比較は、底の比較辺を含む族の始点側と固定 fiber 内でホモトピック。 -/
lemma initialHomComparison_edge_family_homotopy [InnerFibration q] (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      ((vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha) ≫
        leftFibrationInitialSection q c hc y ≫ leftFibrationInitialProjection q c y)
      (initialEdgeBaseSource q c e he y a ha b h)) := by
  obtain ⟨l, _, hp, ⟨H⟩⟩ := exists_initialHomEdgeFamily q c hc e he y a ha b h
  have hl : l ≫ leftFibrationInitialProjection q c y =
      initialEdgeBaseSource q c e he y a ha b h := by
    apply vertexFiber_hom_ext
    rw [Category.assoc]
    exact hp
  have H' := functorHomotopyPostcomp H (leftFibrationInitialProjection q c y)
  simpa only [Category.assoc, hl] using (show Nonempty (SSet.Homotopy _ _) from ⟨H'⟩)

/-- 左 pinched Hom への実際の比較にも、同じ全パラメータの自然性のホモトピーを与える。 -/
lemma initialHomComparison_edge_family_pinched_homotopy [InnerFibration q]
    (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      ((vertexFiberLift q y (a ≫ sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ha) ≫
        leftFibrationInitialHomComparison q c hc y)
      (initialEdgeBaseSource q c e he y a ha b h ≫ (leftFibrationInitialBaseIso q c y).hom)) := by
  obtain ⟨H⟩ := initialHomComparison_edge_family_homotopy q c e he y a ha b h hc
  exact ⟨by simpa only [leftFibrationInitialHomComparison, Category.assoc] using
    functorHomotopyPostcomp H (leftFibrationInitialBaseIso q c y).hom⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
