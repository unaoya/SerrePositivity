module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootedTetrahedron
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTetrahedronFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightHomTriangle

/-!
概要：指定余錐の全 Hom の族を、元の付加比較辺を含む四面体を通して共通部分の Hom 比較へ移す。
方針：終端三角形の族を底を保って延長し、始対象の頂点へ制限した中間 Hom の族と比較する。
規約：指定余錐の余極限性は仮定しない。四面体・元の比較辺・全 Hom パラメータを保持する。
使われ方：共通 path end の共通成分と右境界の高次整合性の照合。
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

/-- 指定余錐の全 Hom の族を共通部分へ制限した、同じ固定終点の余錐族。 -/
def specifiedCoconeCommonHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      coconeMappingSpace (f ≫ (i ≫ p)) y :=
  coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
    cosliceRestrictionFiberMap p j y ≫
      normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) y

/-- 右修正三角形の全 Hom の族を、同じ三角形の共通部分への制限上へ移す。 -/
def specifiedCoconeCommonHomTriangleFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (specifiedCoconeCommonRightTriangle hp p c hc dB dC) :=
  specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
    sliceUnderPostcomp (specifiedCoconeRightTriangle hp p c hc dB dC)
      (normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p))

/-- 共通部分の三角形族の可変終点は、元の全 Hom の余錐族の制限そのもの。 -/
lemma specifiedCoconeCommonHomTriangleFamily_endpoint :
    specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y ≫
        sliceUnderProjection (specifiedCoconeCommonRightTriangle hp p c hc dB dC) =
      specifiedCoconeCommonHomFamily hp p c hc dB dC y ≫
        vertexFiberι (sliceUnderProjection (f ≫ (i ≫ p))) y := by
  have h := congrArg (fun k :
      pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
        sliceUnder (j ≫ p) ↦
      k ≫ normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p))
    (specifiedCoconeRightHomTriangleFamily_endpoint hp p c hc dB dC y)
  simpa only [specifiedCoconeCommonHomTriangleFamily, specifiedCoconeCommonRightTriangle,
    specifiedCoconeCommonHomFamily, Category.assoc, sliceUnderPostcomp_projection,
    normalizedCoconeRestrictionFiber, vertexFiberMap_ι] using h

/-- 同じ全 Hom の族を、元の付加比較辺を前置した実際の四面体全体へ延長する。 -/
def specifiedCoconeRootedHomTetrahedronFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC) :=
  (specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y ≫
    eqToHom (congrArg sliceUnder
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm)) ≫
    relativeTetrahedronTerminalFaceSection (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
      (sliceUnderProjection (f ≫ (i ≫ p)))

/-- 四面体の全 Hom の族の終端面は、元の右修正三角形の族を回収する。 -/
lemma specifiedCoconeRootedHomTetrahedronFamily_terminalFace :
    specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
        sliceUnderRestrict (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 4)) =
      specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y ≫
        eqToHom (congrArg sliceUnder
          (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm) := by
  rw [specifiedCoconeRootedHomTetrahedronFamily, Category.assoc,
    relativeTetrahedronTerminalFaceSection_target, Category.comp_id]

/-- 全 Hom の四面体族の底も、同じ終端面の底を同じ四面体上で延長した族そのもの。 -/
lemma specifiedCoconeRootedHomTetrahedronFamily_base :
    specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
        sliceUnderPostcomp (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
          (sliceUnderProjection (f ≫ (i ≫ p))) =
      (specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y ≫
        eqToHom (congrArg sliceUnder
          (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm)) ≫
        sliceUnderPostcomp
          (stdSimplex.δ (0 : Fin 4) ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
          (sliceUnderProjection (f ≫ (i ≫ p))) ≫
        tetrahedronTerminalFaceSection
          (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC ≫
            sliceUnderProjection (f ≫ (i ≫ p))) := by
  have h := relativeTetrahedronTerminalFaceSection_base
    (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
    (sliceUnderProjection (f ≫ (i ≫ p)))
  have h' := congrArg (fun k ↦
    (specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y ≫
      eqToHom (congrArg sliceUnder
        (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm)) ≫ k) h
  simpa only [specifiedCoconeRootedHomTetrahedronFamily, Category.assoc] using h'

/-- 四面体全体へ延長しても、元の余錐族の共通部分への制限を可変終点として厳密に保つ。 -/
lemma specifiedCoconeRootedHomTetrahedronFamily_endpoint :
    specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
        sliceUnderProjection (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC) =
      specifiedCoconeCommonHomFamily hp p c hc dB dC y ≫
        vertexFiberι (sliceUnderProjection (f ≫ (i ≫ p))) y := by
  rw [specifiedCoconeRootedHomTetrahedronFamily, Category.assoc,
    relativeTetrahedronTerminalFaceSection_projection, Category.assoc,
    sliceUnder_eqToHom_projection
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm,
    specifiedCoconeCommonHomTriangleFamily_endpoint]

/-- 四面体の族の可変終点は、底の指定した終点 y 上に留まる。 -/
lemma specifiedCoconeRootedHomTetrahedronFamily_fixed :
    (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
      sliceUnderProjection (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)) ≫
        sliceUnderProjection (f ≫ (i ≫ p)) = SSet.const y := by
  rw [specifiedCoconeRootedHomTetrahedronFamily_endpoint, Category.assoc,
    vertexFiberι_comp, SSet.comp_const]

/-- 元の付加比較辺を含む四面体の族を、共通部分の始対象を始点とする中間 Hom の族へ移す。 -/
def specifiedCoconeRootedInitialHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      leftFibrationInitialTotal (sliceUnderProjection (f ≫ (i ≫ p))) c y :=
  initialDiagramHomFamily (sliceUnderProjection (f ≫ (i ≫ p))) c
    (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
    (stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)))
    (specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC) y
    (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y)
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)

/-- 中間 Hom の評価は、元の余錐の全 Hom の族の共通部分への制限と厳密に一致する。 -/
lemma specifiedCoconeRootedInitialHomFamily_evaluation :
    specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialEvaluation (sliceUnderProjection (f ≫ (i ≫ p))) c y =
      specifiedCoconeCommonHomFamily hp p c hc dB dC y := by
  rw [specifiedCoconeRootedInitialHomFamily, initialDiagramHomFamily_evaluation]
  apply vertexFiber_hom_ext
  rw [vertexFiberLift_ι, specifiedCoconeRootedHomTetrahedronFamily_endpoint]

/-- 共通部分の Hom 比較は、同じ四面体全体から得た一つの族と全 Hom パラメータでホモトピック。 -/
lemma specifiedCoconeRootedHomComparison_homotopy :
    Nonempty (SSet.Homotopy
      (specifiedCoconeCommonHomFamily hp p c hc dB dC y ≫ coconeMappingSpaceHomComparison c hc y)
      (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
          (leftFibrationInitialBaseIso (sliceUnderProjection (f ≫ (i ≫ p))) c y).hom)) := by
  have he : vertexFiberLift (sliceUnderProjection (f ≫ (i ≫ p))) y
      (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
        sliceUnderProjection (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC))
      (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y) =
        specifiedCoconeCommonHomFamily hp p c hc dB dC y := by
    apply vertexFiber_hom_ext
    rw [vertexFiberLift_ι, specifiedCoconeRootedHomTetrahedronFamily_endpoint]
  have H := initialDiagramHomComparison_homotopy (sliceUnderProjection (f ≫ (i ≫ p))) c
    (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
    (stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)))
    (specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC) y
    (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y)
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y) hc
  simpa only [he, specifiedCoconeRootedInitialHomFamily, coconeMappingSpaceHomComparison] using H

end
end SerrePositivity.InfinityCategories.HomotopyLimits
