module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeBranchComparisons
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTriangleFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedLiftFibreComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftTransportEdge
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightStandardTransportEdge

/-!
概要：指定余錐の実際の右修正二単体に、長辺の全パラメータ族を保つ相対延長を付ける。
方針：比較辺・修正辺・三角形を一つの証明済みデータとして選び、底の右退化を厳密に照合する。
規約：二単体を別の合成へ置き換えず、選んだ同じ二単体を全ての族で使う。
使われ方：元の全 Hom の族の右枝と境界経路の整合性。
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
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 実際の二枝と右修正の合成三角形を、指定余錐を固定して一緒に保持する。 -/
structure SpecifiedCoconeBranchData where
  left : (sliceUnder (i ≫ p)).Edge dB
    ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i)
  right : (sliceUnder (j ≫ p)).Edge dC
    ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j)
  transport : (sliceUnder (j ≫ p)).Edge dC
    (transportedCoconeVertex dC (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val
  triangle : SSet.Edge.CompStruct transport
    (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC) right
  left_projection : (left.map (sliceUnderProjection (i ≫ p))).edge =
    (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge
  right_projection : (right.map (sliceUnderProjection (j ≫ p))).edge =
    (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge
  left_raw : left.edge = (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge
  transport_raw : transport.edge =
    (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge
  triangle_projection : (sliceUnderProjection (j ≫ p)).app (Opposite.op ⦋2⦌) triangle.simplex =
    (SSet.Edge.CompStruct.compId (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).simplex

set_option maxHeartbeats 800000 in
-- 左の厳密な制限と右の修正先を、同じ標準 prism の頂点と同時に照合する。
/-- 標準 prism 自身の二辺と元の修正辺・底の二単体を一緒に保持するデータを構成する。 -/
def specifiedCoconeBranchData : SpecifiedCoconeBranchData hp p c hc dB dC :=
  Classical.choice (by
    let q := sliceUnderProjection (j ≫ p)
    let e := partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
    let v := initialFiberVertexAt q dC dC.vertex rfl
    let w := (cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
      (partialColimitSpecifiedFiberVertex hp p c hc dB dC)
    let k₀ := specifiedCoconeRightStandardTransportEdge hp p c hc dB dC
    obtain ⟨k, t, hk, ht⟩ := exists_compStruct_of_lift_and_fibre_edge q e v
      (transportedCoconeVertex dC e) w k₀
      (specifiedCoconeRightStandardTransportEdge_projection hp p c hc dB dC)
      (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC)
    let kC : (sliceUnder (j ≫ p)).Edge dC
        ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j) :=
      ⟨k.edge, k.src_eq, k.tgt_eq.trans (coconeRestrictionFiber_vertex_val j _
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC))⟩
    refine ⟨{ left := specifiedCoconeLeftTransportEdge hp p c hc dB dC
              right := kC
              transport := k₀
              triangle := SSet.Edge.CompStruct.mk t.simplex t.d₂ ?_ t.d₁
              left_projection := specifiedCoconeLeftTransportEdge_projection hp p c hc dB dC
              right_projection := hk
              left_raw := rfl
              transport_raw := rfl
              triangle_projection := ht }⟩
    have h₀ : (sliceUnder (j ≫ p)).δ 0 t.simplex =
        (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge.val :=
      t.d₀.trans (fibreEdgeInclusion_raw q _
        (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC))
    simpa only [partialColimitSpecifiedCorrectionCosliceEdge, SSet.Edge.edge,
      SSet.Edge.toTruncated] using h₀)


/-- 指定した修正辺そのものを面に持つ、選んだ実際の三角形の全単体表示。 -/
def specifiedCoconeRightTriangle : (Δ[2] : SSet.{u + 1}) ⟶ sliceUnder (j ≫ p) :=
  SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).triangle.simplex

/-- 選んだ右修正三角形の初辺は、元の標準 prism 自身の輸送辺である。 -/
lemma specifiedCoconeRightTriangle_standardFace :
    stdSimplex.δ (2 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm
        (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm,
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₂,
    (specifiedCoconeBranchData hp p c hc dB dC).transport_raw]

/-- 右三角形の長辺は、同じデータに保持した右枝の比較辺。 -/
lemma specifiedCoconeRightTriangle_longEdge :
    stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).right.edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₁

/-- 右三角形の修正面は、元の指定経路自身の辺。 -/
lemma specifiedCoconeRightTriangle_correction :
    stdSimplex.δ (0 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm
        (partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₀

/-- 右三角形の底は、元の span の右脚の右退化そのもの。 -/
lemma specifiedCoconeRightTriangle_base :
    specifiedCoconeRightTriangle hp p c hc dB dC ≫ sliceUnderProjection (j ≫ p) =
      stdSimplex.σ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm
        (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).edge := by
  rw [specifiedCoconeRightTriangle, SSet.yonedaEquiv_symm_comp,
    (specifiedCoconeBranchData hp p c hc dB dC).triangle_projection,
    SSet.Edge.CompStruct.compId_simplex, stdSimplex.σ_comp_yonedaEquiv_symm]

/-- 右枝の長辺上の全余錐族を、指定した同じ右修正三角形全体へ延長する相対切断。 -/
def specifiedCoconeRightTriangleSection :
    sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) ⟶
      sliceUnder (specifiedCoconeRightTriangle hp p c hc dB dC) :=
  relativeDegenerateTriangleSection (specifiedCoconeRightTriangle hp p c hc dB dC)
    (sliceUnderProjection (j ≫ p)) _ (specifiedCoconeRightTriangle_base hp p c hc dB dC)

/-- 指定右三角形の全パラメータ切断は、長辺の族を厳密に回収する。 -/
lemma specifiedCoconeRightTriangleSection_longEdge :
    specifiedCoconeRightTriangleSection hp p c hc dB dC ≫
      sliceUnderRestrict (specifiedCoconeRightTriangle hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 3)) = 𝟙 _ :=
  relativeDegenerateTriangleSection_longEdge _ _ _ _

/-- 指定右三角形の延長は、可変な余錐の終点も全単体で保つ。 -/
lemma specifiedCoconeRightTriangleSection_projection :
    specifiedCoconeRightTriangleSection hp p c hc dB dC ≫
      sliceUnderProjection (specifiedCoconeRightTriangle hp p c hc dB dC) =
        sliceUnderProjection
          (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) :=
  relativeDegenerateTriangleSection_projection _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
