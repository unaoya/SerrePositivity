module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomBasePrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation

/-!
概要：既存の一点の全 Hom の持ち上げを、同じ底の全 Hom 円柱に沿う実際の円柱へ移す。
方針：点下の coslice の族を展開し、同じ join prism で前合成する。
規約：既存の点 Hom の族を新たな輸送へ置き換えず、元の終点と底を厳密に保つ。
使われ方：全始点の輸送作用との比較、指定 fiber 経路に沿う点 Hom 族の変化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 点図式の表示を揃えた底の Hom 同型を展開すると、同じ全 Hom の普遍余錐になる。 -/
lemma leftFibrationInitialBaseIso_inv_uncurry {E B : SSet.{u}}
    (p : E ⟶ B) (d : E _⦋0⦌) (b : B _⦋0⦌) :
    sliceUnderUncurry ((leftFibrationInitialBaseIso p d b).inv ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) b) =
        pointHomBaseCone (p.app (Opposite.op ⦋0⦌) d) b := by
  simp only [leftFibrationInitialBaseIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
    Category.assoc]
  rw [stableCosliceFiberChange_ι, ← Category.assoc, sliceUnderUncurry_eqToHom]
  all_goals first | rfl | exact (SSet.yonedaEquiv_symm_comp d p).symm

variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (d : E _⦋0⦌) (b : B _⦋0⦌)

/-- 既存の全 Hom の持ち上げを展開した、同じ始点 d の余錐族。 -/
def pointHomLiftCone : join (Δ[0] : SSet.{u})
    (pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) ⟶ E :=
  sliceUnderUncurry (leftFibrationPointHomLift p d b ≫
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ p) b)

/-- 展開した元の持ち上げの始点は、元の指定点そのもの。 -/
lemma pointHomLiftCone_source :
    joinInl (Δ[0] : SSet.{u}) _ ≫ pointHomLiftCone p d b = SSet.yonedaEquiv.symm d :=
  sliceUnderUncurry_fixed _

/-- 同じ余錐族の終点は、既存の点 Hom の族そのもの。 -/
lemma pointHomLiftCone_target :
    joinInr (Δ[0] : SSet.{u}) _ ≫ pointHomLiftCone p d b =
      leftFibrationPointHomFamily p d b ≫ vertexFiberι p b := by
  rw [pointHomLiftCone, sliceUnderUncurry_projection]
  simp only [leftFibrationPointHomFamily, Category.assoc,
    leftFibrationInitialEvaluation, vertexFiberMap_ι]

/-- 既存の持ち上げの底も、同じ全 Hom の普遍余錐へ厳密に一致する。 -/
lemma pointHomLiftCone_projection :
    pointHomLiftCone p d b ≫ p = pointHomBaseCone (p.app (Opposite.op ⦋0⦌) d) b := by
  rw [pointHomLiftCone, ← sliceUnderUncurry_postcomp]
  have h : (leftFibrationPointHomLift p d b ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ p) b) ≫
        sliceUnderPostcomp (SSet.yonedaEquiv.symm d) p =
      (leftFibrationInitialBaseIso p d b).inv ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) b := by
    rw [← leftFibrationPointHomLift_projection p d b]
    simp only [Category.assoc, leftFibrationInitialProjection, vertexFiberMap_ι]
  rw [h, leftFibrationInitialBaseIso_inv_uncurry]

/-- 既存の全 Hom の持ち上げを、その同じ終点を保つ実際の円柱として表示する。 -/
def pointHomLiftPrism : (Δ[1] : SSet.{u}) ⊗
    pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b ⟶ E :=
  cofinalPointJoinPrism _ ≫ pointHomLiftCone p d b

/-- 元の点 Hom の円柱の始点は、元の点 d 上で定値。 -/
lemma pointHomLiftPrism_zero :
    prismEndpoint 0 _ ≫ pointHomLiftPrism p d b = SSet.const d := by
  rw [pointHomLiftPrism, ← Category.assoc, cofinalPointJoinPrism_zero, Category.assoc,
    pointHomLiftCone_source, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 元の円柱の終点は、同じ既存の全 Hom の族。 -/
lemma pointHomLiftPrism_one :
    prismEndpoint 1 _ ≫ pointHomLiftPrism p d b =
      leftFibrationPointHomFamily p d b ≫ vertexFiberι p b := by
  rw [pointHomLiftPrism, ← Category.assoc, cofinalPointJoinPrism_one, pointHomLiftCone_target]

/-- 元の点 Hom 円柱の底は、同じ全 Hom の底の円柱そのもの。 -/
lemma pointHomLiftPrism_projection :
    pointHomLiftPrism p d b ≫ p = pointHomBasePrism (p.app (Opposite.op ⦋0⦌) d) b := by
  rw [pointHomLiftPrism, Category.assoc, pointHomLiftCone_projection]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
