module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomLiftPrism

/-!
概要：比較辺の終端の全係数を、底への射影を取らず元の余錐族へ戻す。
方針：始点固定 Hom の写像を展開し、coslice の uncurry を後合成と交換する。
規約：上の全族の厳密な等式。使われ方：左右の長辺族の終端係数の照合。
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

omit [Quasicategory B] in
/-- 終端の全余錐族を展開すると、元の全 Hom の余錐族の関手による像になる。 -/
lemma pointRestrictionEdgeFamily_uncurry :
    sliceUnderUncurry (pointRestrictionEdgeFamily p q r hr d e y) =
      pointHomLiftCone p d y ≫ r := by
  let s := leftFibrationPointHomLift p d y
  let z := r.app (Opposite.op ⦋0⦌) d
  let I := vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ p) y
  have hm : (s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y =
      (s ≫ I) ≫ stableCoslicePostcomp (SSet.yonedaEquiv.symm d) r
        (SSet.yonedaEquiv.symm z) (SSet.yonedaEquiv_symm_comp d r) := by
    rw [Category.assoc, leftFibrationInitialTotalMap, vertexFiberMap_ι, ← Category.assoc]
  change sliceUnderUncurry
    (((s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y) ≫
      eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm.symm)) = _
  rw [sliceUnderUncurry_eqToHom e.δ_zero_yonedaEquiv_symm.symm, hm,
    stableCoslicePostcomp_uncurry]
  rfl

/-- 比較辺全体の終端制限も、底を忘れずに元の同じ全族を回収する。 -/
lemma pointRestrictionFullEdgeFamily_tip_total_uncurry [InnerFibration q] :
    joinMap (stdSimplex.δ (0 : Fin 2))
        (𝟙 (pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y)) ≫
      sliceUnderUncurry (pointRestrictionFullEdgeFamily p q r hr d e y) =
        pointHomLiftCone p d y ≫ r := by
  rw [← sliceUnderUncurry_restrict, pointRestrictionFullEdgeFamily_target,
    pointRestrictionEdgeFamily_uncurry]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
