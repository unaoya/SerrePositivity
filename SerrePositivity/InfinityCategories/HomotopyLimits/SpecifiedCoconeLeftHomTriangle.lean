module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootedTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRightCosliceSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily

/-!
概要：標準の左輸送辺の全 Hom の族を、元の native な左二単体を覆う三角形全体へ延長する。
方針：元の全 Hom を同じ左辺に沿って持ち上げ、終端辺と底を保つ相対切断を合成する。
規約：始対象比較の評価、元の付加辺、標準輸送辺、底の二単体を全て保持する。
使われ方：左 HL の評価固定円柱を、同じ左三角形の中間 Hom 族と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "r" => sliceUnderRestrict (i ≫ p) f
local notation "k" => specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "s" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "W" => coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y

/-- 元の全 Hom の族を標準の左輸送辺全体へ、底の同じ合成族を保って持ち上げる。 -/
def specifiedCoconeLeftFullHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (SSet.yonedaEquiv.symm (k).edge) :=
  pointRestrictionFullEdgeFamily (sliceUnderProjection p) (sliceUnderProjection (i ≫ p))
    (sliceUnderRestrict p i) (sliceUnderRestrict_projection p i)
    (partialColimitSpecifiedPathCocone hp p c hc dB dC) k y

/-- 左辺全体の族の可変終点は、元の全 Hom の族の左制限そのもの。 -/
lemma specifiedCoconeLeftFullHomFamily_endpoint :
    specifiedCoconeLeftFullHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (k).edge) =
      W ≫ cosliceRestrictionFiberMap p i y ≫ vertexFiberι (sliceUnderProjection (i ≫ p)) y :=
  pointRestrictionFullEdgeFamily_endpoint _ _ _ _ _ _ _

/-- 標準の左辺の全族を、その辺とともに共通部分へ制限する。 -/
def specifiedCoconeLeftCommonEdgeFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (SSet.yonedaEquiv.symm (k).edge ≫ r) :=
  specifiedCoconeLeftFullHomFamily hp p c hc dB dC y ≫
    sliceUnderPostcomp (SSet.yonedaEquiv.symm (k).edge) r

/-- 共通部分の辺の族の終点は、元の族の左からの二段階制限。 -/
lemma specifiedCoconeLeftCommonEdgeFamily_endpoint :
    specifiedCoconeLeftCommonEdgeFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (k).edge ≫ r) =
      (W ≫ cosliceRestrictionFiberMap p i y ≫ cosliceRestrictionFiberMap (i ≫ p) f y) ≫
        vertexFiberι q y := by
  have h := congrArg (fun z ↦ z ≫ r)
    (specifiedCoconeLeftFullHomFamily_endpoint hp p c hc dB dC y)
  have hs : specifiedCoconeLeftCommonEdgeFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (k).edge ≫ r) =
      (W ≫ cosliceRestrictionFiberMap p i y ≫
        vertexFiberι (sliceUnderProjection (i ≫ p)) y) ≫ r := by
    simpa only [specifiedCoconeLeftCommonEdgeFamily, Category.assoc,
      sliceUnderPostcomp_projection] using h
  have hr : cosliceRestrictionFiberMap (i ≫ p) f y ≫ vertexFiberι q y =
      vertexFiberι (sliceUnderProjection (i ≫ p)) y ≫ r := vertexFiberMap_ι _ _ _ _ _
  refine hs.trans ?_
  calc
    _ = (W ≫ cosliceRestrictionFiberMap p i y) ≫
        (vertexFiberι (sliceUnderProjection (i ≫ p)) y ≫ r) := by simp only [Category.assoc]
    _ = (W ≫ cosliceRestrictionFiberMap p i y) ≫
        (cosliceRestrictionFiberMap (i ≫ p) f y ≫ vertexFiberι q y) :=
      congrArg (fun z ↦ (W ≫ cosliceRestrictionFiberMap p i y) ≫ z) hr.symm
    _ = _ := by simp only [Category.assoc]

/-- 左からの共通部分への全 Hom の制限は、既存の同じ共通族に厳密に一致する。 -/
lemma specifiedCoconeLeftCommonHomFamily_eq :
    W ≫ cosliceRestrictionFiberMap p i y ≫ cosliceRestrictionFiberMap (i ≫ p) f y = V :=
  congrArg (fun z ↦ W ≫ z) (coconeMappingShapePushout_isPullback hp p y).w

/-- 元の左辺の全 Hom の族を、同じ三角形の終端面の表示へ移す。 -/
def specifiedCoconeLeftTerminalHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (stdSimplex.δ (0 : Fin 3) ≫ s) :=
  specifiedCoconeLeftCommonEdgeFamily hp p c hc dB dC y ≫ eqToHom
    (congrArg sliceUnder (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC).symm)

/-- 元の三角形の終端辺と底を厳密に保つ、全 Hom の三角形族。 -/
def specifiedCoconeLeftRootedHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶ sliceUnder s :=
  specifiedCoconeLeftTerminalHomFamily hp p c hc dB dC y ≫
    relativeRightCosliceSection s q (stdSimplex.δ (0 : Fin 3)) triangleTerminalFace_rightAnodyne

/-- 終端辺へ戻すと、同じ標準左辺の全パラメータ族を回収する。 -/
lemma specifiedCoconeLeftRootedHomFamily_terminal :
    specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        sliceUnderRestrict s (stdSimplex.δ (0 : Fin 3)) =
      specifiedCoconeLeftTerminalHomFamily hp p c hc dB dC y := by
  rw [specifiedCoconeLeftRootedHomFamily, Category.assoc,
    relativeRightCosliceSection_boundary, Category.comp_id]

/-- 左三角形全体の族は、可変終点で元の同じ共通族を厳密に回収する。 -/
lemma specifiedCoconeLeftRootedHomFamily_endpoint :
    specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫ sliceUnderProjection s =
      V ≫ vertexFiberι q y := by
  rw [specifiedCoconeLeftRootedHomFamily, Category.assoc,
    relativeRightCosliceSection_projection, specifiedCoconeLeftTerminalHomFamily, Category.assoc,
    sliceUnder_eqToHom_projection (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC).symm]
  exact (specifiedCoconeLeftCommonEdgeFamily_endpoint hp p c hc dB dC y).trans
    (congrArg (fun z ↦ z ≫ vertexFiberι q y)
      (specifiedCoconeLeftCommonHomFamily_eq hp p c hc dB dC y))

/-- 底の三角形族も、元の終端族から同じ切断で延長したもの。 -/
lemma specifiedCoconeLeftRootedHomFamily_base :
    specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫ sliceUnderPostcomp s q =
      specifiedCoconeLeftTerminalHomFamily hp p c hc dB dC y ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 3) ≫ s) q ≫
          rightCosliceSection (s ≫ q) (stdSimplex.δ (0 : Fin 3))
            triangleTerminalFace_rightAnodyne := by
  rw [specifiedCoconeLeftRootedHomFamily, Category.assoc, relativeRightCosliceSection_base]

/-- 同じ全 Hom の三角形族は、底の指定終点上に留まる。 -/
lemma specifiedCoconeLeftRootedHomFamily_fixed :
    (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫ sliceUnderProjection s) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeLeftRootedHomFamily_endpoint, Category.assoc, vertexFiberι_comp,
    SSet.comp_const]

/-- 元の付加辺を始点に持つ、左三角形全体からの中間 Hom の族。 -/
def specifiedCoconeLeftInitialHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      leftFibrationInitialTotal q c y :=
  initialDiagramHomFamily q c s (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    (specifiedCoconeLeftRootedTriangle_initial hp p c hc dB dC) y
    (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)

/-- 中間 Hom の評価も、元の指定余錐の同じ共通族そのもの。 -/
lemma specifiedCoconeLeftInitialHomFamily_evaluation :
    specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialEvaluation q c y = V := by
  rw [specifiedCoconeLeftInitialHomFamily, initialDiagramHomFamily_evaluation]
  apply vertexFiber_hom_ext
  rw [vertexFiberLift_ι, specifiedCoconeLeftRootedHomFamily_endpoint]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
