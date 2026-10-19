module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomPointFamilyComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomCospanIso

/-!
概要：任意の頂点の全 Hom の族を底上の関手で制限し、比較辺の終点側へ表示する。
方針：始点固定の比較 span の写像に全 Hom の持ち上げを入力し、評価と底への射影を計算する。
規約：元の頂点の始対象性は不要。使われ方：貼った余錐から部分図式への全 Hom の制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}}
  (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

/-- 任意の頂点からの全 Hom の族を関手で写し、比較辺の終点側で表示する。 -/
def pointRestrictionEdgeFamily :
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y ⟶
      sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) :=
  leftFibrationPointHomLift p d y ≫
    leftFibrationInitialTotalMap p q r hr d (r.app (Opposite.op ⦋0⦌) d) rfl y ≫
    vertexFiberι (sliceUnderProjection
      (SSet.yonedaEquiv.symm (r.app (Opposite.op ⦋0⦌) d)) ≫ q) y ≫
    eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm.symm)

/-- 制限した族の終点は、元の全 Hom の族の関手による像そのもの。 -/
lemma pointRestrictionEdgeFamily_endpoint :
    pointRestrictionEdgeFamily p q r hr d e y ≫
        sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) =
      leftFibrationPointHomFamily p d y ≫ vertexFiberMap p q r hr y ≫ vertexFiberι q y := by
  calc
    _ = leftFibrationPointHomLift p d y ≫
        (leftFibrationInitialTotalMap p q r hr d (r.app (Opposite.op ⦋0⦌) d) rfl y ≫
          leftFibrationInitialEvaluation q (r.app (Opposite.op ⦋0⦌) d) y) ≫
        vertexFiberι q y := by
      simp only [pointRestrictionEdgeFamily, Category.assoc,
        leftFibrationInitialEvaluation, vertexFiberMap_ι]
      erw [sliceUnder_eqToHom_projection e.δ_zero_yonedaEquiv_symm.symm]
    _ = _ := by
      simp only [leftFibrationInitialTotalMap_evaluation, leftFibrationPointHomFamily,
        Category.assoc]

/-- 制限した全 Hom の族は、底の指定終点上に留まる。 -/
lemma pointRestrictionEdgeFamily_fixed :
    (pointRestrictionEdgeFamily p q r hr d e y ≫
      sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge)) ≫ q =
        SSet.const y := by
  rw [pointRestrictionEdgeFamily_endpoint, Category.assoc, Category.assoc,
    vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 固定終点の族として読み直しても、元の全 Hom の族の制限を回収する。 -/
lemma pointRestrictionEdgeFamily_vertexFiberLift :
    vertexFiberLift q y
      (pointRestrictionEdgeFamily p q r hr d e y ≫
        sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge))
      (pointRestrictionEdgeFamily_fixed p q r hr d e y) =
        leftFibrationPointHomFamily p d y ≫ vertexFiberMap p q r hr y := by
  apply vertexFiber_hom_ext q y
  rw [vertexFiberLift_ι, pointRestrictionEdgeFamily_endpoint, Category.assoc]

/-- 制限した族の底への射影を、元の全 Hom のパラメータとして表示する。 -/
lemma pointRestrictionEdgeFamily_base :
    pointRestrictionEdgeFamily p q r hr d e y ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q =
      ((leftFibrationInitialBaseIso p d y).inv ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y) ≫
          eqToHom (congrArg sliceUnder (initialRestrictionEdgeBase_eq p q r hr d e)) := by
  let s := leftFibrationPointHomLift p d y
  let z := r.app (Opposite.op ⦋0⦌) d
  let I := vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ p) y
  have hm : (s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y =
      (s ≫ I) ≫ stableCoslicePostcomp (SSet.yonedaEquiv.symm d) r
        (SSet.yonedaEquiv.symm z) (SSet.yonedaEquiv_symm_comp d r) := by
    rw [Category.assoc, leftFibrationInitialTotalMap, vertexFiberMap_ι, ← Category.assoc]
  have ha : sliceUnderUncurry (pointRestrictionEdgeFamily p q r hr d e y) =
      sliceUnderUncurry (s ≫ I) ≫ r := by
    change sliceUnderUncurry
      (((s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y) ≫
        eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm.symm)) = _
    rw [sliceUnderUncurry_eqToHom e.δ_zero_yonedaEquiv_symm.symm, hm,
      stableCoslicePostcomp_uncurry]
  have hp : ((leftFibrationInitialBaseIso p d y).inv ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y) =
      (s ≫ I) ≫ sliceUnderPostcomp (SSet.yonedaEquiv.symm d) p := by
    rw [← leftFibrationPointHomLift_projection p d y, Category.assoc,
      leftFibrationInitialProjection, vertexFiberMap_ι, ← Category.assoc]
  apply sliceUnderUncurry_injective
  rw [sliceUnderUncurry_postcomp, ha, Category.assoc, hr,
    sliceUnderUncurry_eqToHom (initialRestrictionEdgeBase_eq p q r hr d e), hp,
    sliceUnderUncurry_postcomp]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
