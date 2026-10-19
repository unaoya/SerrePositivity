module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeTriangleFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeLift

/-!
概要：指定余錐の全 Hom の族を、元の右修正辺と合成二単体を同時に保持する三角形の族へする。
方針：右比較辺全体へ底の合成族を保って持ち上げ、同じ右三角形の相対切断を合成する。
規約：元の余錐の余極限性も Hom のパラメータの充填性も使わない。
使われ方：右枝の Hom の比較と指定境界経路を共通 end で結ぶ際の三面の整合性。
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

/-- 特定の指定余錐の全 Hom を、底の元の合成族を保って右比較辺全体へ持ち上げた族。 -/
def specifiedCoconeRightFullHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).right.edge) :=
  pointRestrictionFullEdgeFamily (sliceUnderProjection p) (sliceUnderProjection (j ≫ p))
    (sliceUnderRestrict p j) (sliceUnderRestrict_projection p j)
    (partialColimitSpecifiedPathCocone hp p c hc dB dC)
    (specifiedCoconeBranchData hp p c hc dB dC).right y

/-- 同じ族を、選んだ実際の三角形の長辺側の表示へ移す。 -/
def specifiedCoconeRightHomLongEdgeFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) :=
  specifiedCoconeRightFullHomFamily hp p c hc dB dC y ≫
    eqToHom (congrArg sliceUnder (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm)

/-- 指定余錐の全 Hom を同じ実際の右二単体全体に延長した、整合した三面を持つ族。 -/
def specifiedCoconeRightHomTriangleFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (specifiedCoconeRightTriangle hp p c hc dB dC) :=
  specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y ≫
    specifiedCoconeRightTriangleSection hp p c hc dB dC

/-- 全 Hom の三角形族の長辺は、入力した同じ右比較辺の全 Hom の族。 -/
lemma specifiedCoconeRightHomTriangleFamily_longEdge :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        sliceUnderRestrict (specifiedCoconeRightTriangle hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 3)) =
      specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y := by
  rw [specifiedCoconeRightHomTriangleFamily, Category.assoc,
    specifiedCoconeRightTriangleSection_longEdge, Category.comp_id]

/-- 三角形の全 Hom の族の可変終点は、元の余錐族の右枝への制限そのもの。 -/
lemma specifiedCoconeRightHomTriangleFamily_endpoint :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        sliceUnderProjection (specifiedCoconeRightTriangle hp p c hc dB dC) =
      coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
        cosliceRestrictionFiberMap p j y ≫ vertexFiberι (sliceUnderProjection (j ≫ p)) y := by
  rw [specifiedCoconeRightHomTriangleFamily, Category.assoc,
    specifiedCoconeRightTriangleSection_projection, specifiedCoconeRightHomLongEdgeFamily,
    Category.assoc, sliceUnder_eqToHom_projection
      (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm]
  exact pointRestrictionFullEdgeFamily_endpoint (sliceUnderProjection p)
    (sliceUnderProjection (j ≫ p)) (sliceUnderRestrict p j) (sliceUnderRestrict_projection p j)
    (partialColimitSpecifiedPathCocone hp p c hc dB dC)
    (specifiedCoconeBranchData hp p c hc dB dC).right y

/-- 三角形の全 Hom の族の底も、入力した長辺の底を元の右退化で延長した族そのもの。 -/
lemma specifiedCoconeRightHomTriangleFamily_base :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        sliceUnderPostcomp (specifiedCoconeRightTriangle hp p c hc dB dC)
          (sliceUnderProjection (j ≫ p)) =
      retractedCosliceBaseFamily (specifiedCoconeRightTriangle hp p c hc dB dC)
        (sliceUnderProjection (j ≫ p)) (stdSimplex.δ (1 : Fin 3)) (stdSimplex.σ (1 : Fin 2))
        (triangleBase_retraction _ _ _ (specifiedCoconeRightTriangle_base hp p c hc dB dC))
        (specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y) := by
  have h := relativeDegenerateTriangleSection_base
    (specifiedCoconeRightTriangle hp p c hc dB dC) (sliceUnderProjection (j ≫ p)) _
    (specifiedCoconeRightTriangle_base hp p c hc dB dC)
  have h' := congrArg (fun k ↦ specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y ≫ k) h
  simpa only [specifiedCoconeRightHomTriangleFamily, specifiedCoconeRightTriangleSection,
    retractedCosliceBaseFamily, Category.assoc] using h'

/-- 三角形の修正面を、元の指定経路の辺上の全 Hom の族として取り出す。 -/
def specifiedCoconeCorrectionFullHomFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (SSet.yonedaEquiv.symm
        (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge) :=
  specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
    normalizedCoconeRestriction (specifiedCoconeRightTriangle hp p c hc dB dC)
      (stdSimplex.δ (0 : Fin 3)) (specifiedCoconeRightTriangle_correction hp p c hc dB dC)

/-- 元の指定修正辺上の族は、可変終点で元の全 Hom の族の右制限を厳密に回収する。 -/
lemma specifiedCoconeCorrectionFullHomFamily_endpoint :
    specifiedCoconeCorrectionFullHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm
          (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge) =
      coconePointHomFamily (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
        cosliceRestrictionFiberMap p j y ≫ vertexFiberι (sliceUnderProjection (j ≫ p)) y := by
  rw [specifiedCoconeCorrectionFullHomFamily, Category.assoc,
    normalizedCoconeRestriction_projection, specifiedCoconeRightHomTriangleFamily_endpoint]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
