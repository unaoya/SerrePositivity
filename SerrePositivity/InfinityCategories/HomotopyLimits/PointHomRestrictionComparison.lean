module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomRestrictionFamily

/-!
概要：任意の頂点からの全 Hom の族の制限を、実際の比較辺による前合成と照合する。
方針：底の点図式の表示変更を fiber に移し、始対象の Hom 比較の相対ホモトピーを適用する。
規約：元の頂点の始対象性は要求しない。使われ方：貼った余錐の各枝の普遍点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 元の全 Hom のパラメータを、比較辺の底の終点の点図式で表示する。 -/
def pointRestrictionBaseHom :
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶
      coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q)) y :=
  (leftFibrationInitialBaseIso p d y).inv ≫
    eqToHom (congrArg (fun t ↦ vertexFiber (sliceUnderProjection t) y)
      (initialRestrictionEdgeBase_eq p q r hr d e))

omit [Quasicategory B] in
/-- この表示の包含は、全 Hom の族を関手で写した底への射影と一致。 -/
lemma pointRestrictionBaseHom_ι :
    pointRestrictionEdgeFamily p q r hr d e y ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q =
      pointRestrictionBaseHom p q r hr d e y ≫
        vertexFiberι (sliceUnderProjection
          (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q))) y := by
  rw [pointRestrictionEdgeFamily_base]
  have hh := stableCosliceFiberChange_ι (initialRestrictionEdgeBase_eq p q r hr d e) y
  simpa only [pointRestrictionBaseHom, Category.assoc] using
    congrArg (fun f ↦ (leftFibrationInitialBaseIso p d y).inv ≫ f) hh.symm

omit [LeftFibration p] in
/-- 底の表示を戻すと、比較辺による左 Hom の既存の前合成そのものを得る。 -/
lemma pointRestrictionBaseHom_precomposition :
    pointRestrictionBaseHom p q r hr d e y ≫
        cosliceEdgeFiberPrecomposition (SSet.yonedaEquiv.symm e.edge ≫ q)
          (SSet.yonedaEquiv.symm c ≫ q)
          (stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q))
          (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl y ≫
        (leftFibrationInitialBaseIso q c y).hom =
      initialRestrictionHomPrecomposition p q r hr d e y := by
  have hh := cosliceEdgeFiberPrecomposition_points (SSet.yonedaEquiv.symm e.edge ≫ q)
    (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm])
    (initialRestrictionEdgeBase_eq p q r hr d e).symm
    (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) rfl
    rfl (initialRestrictionEdgeBase_eq p q r hr d e) y
  simp only [pointCoconeMappingIso, eqToIso_refl, Iso.refl_hom, eqToIso.hom] at hh
  erw [Category.comp_id] at hh
  simpa only [pointRestrictionBaseHom, initialRestrictionHomPrecomposition,
    Category.assoc] using congrArg (fun f ↦
      (leftFibrationInitialBaseIso p d y).inv ≫ f ≫ (leftFibrationInitialBaseIso q c y).hom) hh.symm

/-- 任意の元の頂点の全 Hom の族を制限し始対象の Hom 比較で測ると、実際の辺の前合成とホモトピック。 -/
lemma pointHomFamily_restriction_comparison_homotopy [InnerFibration q] (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      ((leftFibrationPointHomFamily p d y ≫ vertexFiberMap p q r hr y) ≫
        leftFibrationInitialHomComparison q c hc y)
      (initialRestrictionHomPrecomposition p q r hr d e y)) := by
  have H := initialHomComparison_pointFamily_homotopy q c
    (SSet.yonedaEquiv.symm e.edge) e.δ_one_yonedaEquiv_symm y
    (pointRestrictionEdgeFamily p q r hr d e y)
    (pointRestrictionEdgeFamily_fixed p q r hr d e y)
    (pointRestrictionBaseHom p q r hr d e y)
    (pointRestrictionBaseHom_ι p q r hr d e y) hc
  rwa [pointRestrictionEdgeFamily_vertexFiberLift, pointRestrictionBaseHom_precomposition] at H

end
end SerrePositivity.InfinityCategories.HomotopyLimits
