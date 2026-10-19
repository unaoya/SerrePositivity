module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFiberPrecomposition

/-!
概要：底上の関手による fiber の作用と、実際の比較辺による左 Hom の前合成の正方形を結ぶ。
方針：比較辺の合成三角形の族を元の Hom 比較で評価し、固定終点の前合成を因子として取り出す。
規約：全単体の射の等式と単体的ホモトピーを使う。始点の像には始対象性を要求しない。
使われ方：部分余極限対象の span の Hom 図式と余錐空間の引き戻しを比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 実際の比較辺の底への像による、左 pinched Hom の前合成。 -/
def initialRestrictionHomPrecomposition :
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶
      pinchedHomLeft (q.app (Opposite.op ⦋0⦌) c) y :=
  (leftFibrationInitialBaseIso p d y).inv ≫
    cosliceEdgeFiberPrecomposition (SSet.yonedaEquiv.symm e.edge ≫ q)
      (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm d ≫ p)
      (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm])
      (initialRestrictionEdgeBase_eq p q r hr d e).symm y ≫
    (leftFibrationInitialBaseIso q c y).hom

/-- 底の合成三角形の始点側は、元の比較 span の射影に固定終点の前合成を続けたもの。 -/
lemma initialRestrictionEdgeBaseSource_eq :
    initialEdgeBaseSource q c (SSet.yonedaEquiv.symm e.edge) e.δ_one_yonedaEquiv_symm y
        (initialRestrictionEdgeFamily p q r hr d hd e y)
        (initialRestrictionEdgeFamily_fixed p q r hr d hd e y)
        (initialRestrictionBaseTriangle p q r hr d hd e y)
        (initialRestrictionBaseTriangle_target p q r hr d hd e y) =
      leftFibrationInitialSection p d hd y ≫ leftFibrationInitialProjection p d y ≫
        cosliceEdgeFiberPrecomposition (SSet.yonedaEquiv.symm e.edge ≫ q)
          (SSet.yonedaEquiv.symm c ≫ q) (SSet.yonedaEquiv.symm d ≫ p)
          (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm])
          (initialRestrictionEdgeBase_eq p q r hr d e).symm y := by
  apply vertexFiber_hom_ext
  rw [initialEdgeBaseSource, vertexFiberLift_ι, Category.assoc,
    Category.assoc, cosliceEdgeFiberPrecomposition_ι]
  change (initialRestrictionEdgeFamily p q r hr d hd e y ≫
      sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q) ≫
      cosliceEdgeSection (SSet.yonedaEquiv.symm e.edge ≫ q) ≫
      normalizedCoconeRestriction (SSet.yonedaEquiv.symm e.edge ≫ q)
        (stdSimplex.δ (1 : Fin 2)) (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm]) = _
  rw [initialRestrictionEdgeFamily_base]
  simp only [cosliceEdgePrecompositionAt, cosliceEdgePrecomposition,
    normalizedCoconeRestriction, Category.assoc]

/-- 比較辺から作った Hom の族は、元の Hom 比較と実際の辺による前合成の合成そのもの。 -/
lemma initialRestrictionEdgeHomFamily_eq :
    initialRestrictionEdgeHomFamily p q r hr d hd e y =
      leftFibrationInitialHomComparison p d hd y ≫
        initialRestrictionHomPrecomposition p q r hr d e y := by
  rw [initialRestrictionEdgeHomFamily, initialRestrictionEdgeBaseSource_eq]
  simp only [leftFibrationInitialHomComparison, initialRestrictionHomPrecomposition,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- Hom 比較の正方形は、底の実際の比較辺による前合成と全パラメータで可換。 -/
lemma initialRestrictionHomComparison_square [InnerFibration q] (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      (vertexFiberMap p q r hr y ≫ leftFibrationInitialHomComparison q c hc y)
      (leftFibrationInitialHomComparison p d hd y ≫
        initialRestrictionHomPrecomposition p q r hr d e y)) := by
  have H := initialRestrictionHomComparison_homotopy p q r hr d hd e y hc
  rwa [initialRestrictionEdgeHomFamily_eq] at H

end
end SerrePositivity.InfinityCategories.HomotopyLimits
