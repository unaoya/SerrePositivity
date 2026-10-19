module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RootedHomRootCoordinates
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeTip

/-!
概要：指定余錐の全 Hom の四面体族を、元の native な共通脚の余錐族へ制限する。
方針：辺 03 とその両端の座標を使い、始対象の中間 Hom と元の全 Hom パラメータを計算する。
規約：共通脚の辺と元の余錐を選び直さず、固定終点も厳密に保持する。
使われ方：共通成分の Hom 比較を native な共通脚の実際の前合成へ移す。
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

/-- 全 Hom の四面体族の底を、元の native な共通脚そのものの上へ制限した族。 -/
def specifiedCoconeRootBaseEdgeFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (specifiedCoconeNativeRootEdge hp p c hc dB dC) :=
  (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
    sliceUnderPostcomp (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
      (sliceUnderProjection (f ≫ (i ≫ p)))) ≫
    normalizedCoconeRestriction
      (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC ≫
        sliceUnderProjection (f ≫ (i ≫ p))) tetrahedronRootEdge
      (specifiedCoconeRootedTetrahedron_rootEdge hp p c hc dB dC)

/-- 共通脚上の全 Hom の族は、元の終点 y を保つ。 -/
lemma specifiedCoconeRootBaseEdgeFamily_fixed :
    specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y ≫
      sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC) = SSet.const y := by
  simpa only [specifiedCoconeRootBaseEdgeFamily, Category.assoc,
    normalizedCoconeRestriction_projection, sliceUnderPostcomp_projection] using
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)

/-- 元の共通脚の辺全体の固定終点余錐空間に属する全 Hom の族。 -/
def specifiedCoconeRootBaseEdgeFiberFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      coconeMappingSpace (specifiedCoconeNativeRootEdge hp p c hc dB dC) y :=
  vertexFiberLift _ y (specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y)
    (specifiedCoconeRootBaseEdgeFamily_fixed hp p c hc dB dC y)

/-- 共通脚の始点制限は、同じ四面体から得た始対象の中間 Hom の底を厳密に回収する。 -/
lemma specifiedCoconeRootBaseEdgeFamily_source :
    specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) =
      specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
          vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y := by
  have h := initialDiagramHomFamily_base (sliceUnderProjection (f ≫ (i ≫ p))) c
    (specifiedCoconeRootedRightTetrahedron hp p c hc dB dC)
    (stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)))
    (specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC) y
    (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y)
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)
  have h' : specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
      leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
        vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y = _ := h
  refine Eq.trans ?_ h'.symm
  apply sliceUnderUncurry_injective (coconeVertexDiagram c)
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeRootBaseEdgeFamily,
    normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    ← Category.assoc, ← joinMap_comp, Category.comp_id, tetrahedronRootEdge_source]

/-- 固定終点の共通脚の始点制限も、同じ中間 Hom の射影そのもの。 -/
lemma specifiedCoconeRootBaseEdgeFiberFamily_source :
    specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y =
      specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y := by
  apply vertexFiber_hom_ext
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  have hι := vertexFiberLift_ι
    (sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC)) y
    (specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y)
    (specifiedCoconeRootBaseEdgeFamily_fixed hp p c hc dB dC y)
  have h := congrArg (fun a :
      pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
        sliceUnder (specifiedCoconeNativeRootEdge hp p c hc dB dC) ↦
      a ≫ normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)) hι
  simpa only [Category.assoc, specifiedCoconeRootBaseEdgeFiberFamily] using
    h.trans (specifiedCoconeRootBaseEdgeFamily_source hp p c hc dB dC y)

/-- 共通脚の終点制限は、元の指定余錐の全 Hom の底のパラメータそのものを回収する。 -/
lemma specifiedCoconeRootBaseEdgeFamily_target :
    specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) =
      (leftFibrationInitialBaseIso (sliceUnderProjection p)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) y).inv ≫
        vertexFiberι (sliceUnderProjection
          (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))) y := by
  let d := partialColimitSpecifiedPathCocone hp p c hc dB dC
  let T := pinchedHomLeft d.vertex y
  let Q := sliceUnderProjection (f ≫ (i ≫ p))
  let G := sliceUnderProjection (j ≫ p)
  let F := specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
  let C := specifiedCoconeCommonHomTriangleFamily hp p c hc dB dC y
  let R := specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y
  let L := specifiedCoconeRightFullHomFamily hp p c hc dB dC y
  have hf : joinMap (stdSimplex.δ (0 : Fin 4)) (𝟙 T) ≫ sliceUnderUncurry F =
      sliceUnderUncurry C := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeRootedHomTetrahedronFamily_terminalFace hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_eqToHom
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm] at h
    exact h
  have hl : joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 T) ≫ sliceUnderUncurry R =
      sliceUnderUncurry L := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeRightHomTriangleFamily_longEdge hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, specifiedCoconeRightHomLongEdgeFamily,
      sliceUnderUncurry_eqToHom
        (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm] at h
    exact h
  have hC : sliceUnderUncurry C ≫ Q = sliceUnderUncurry R ≫ G := by
    dsimp only [C, Q, R, G]
    rw [specifiedCoconeCommonHomTriangleFamily, sliceUnderUncurry_postcomp,
      Category.assoc, normalizedCoconeRestriction_projection]
  have htip := pointRestrictionFullEdgeFamily_tip_uncurry (c := dC)
    (sliceUnderProjection p) (sliceUnderProjection (j ≫ p)) (sliceUnderRestrict p j)
    (sliceUnderRestrict_projection p j) (partialColimitSpecifiedPathCocone hp p c hc dB dC)
    (specifiedCoconeBranchData hp p c hc dB dC).right y
  have hjoin {K L M : SSet.{u + 1}} (a : K ⟶ L) (b : L ⟶ M) :
      joinMap (a ≫ b) (𝟙 T) = joinMap a (𝟙 T) ≫ joinMap b (𝟙 T) := by
    simpa only [Category.comp_id] using joinMap_comp a b (𝟙 T) (𝟙 T)
  have hfa := congrArg (fun a : join (Δ[2] : SSet.{u + 1}) T ⟶ sliceUnder (f ≫ (i ≫ p)) ↦
    a ≫ Q) hf
  have hla := congrArg (fun a : join (Δ[1] : SSet.{u + 1}) T ⟶ sliceUnder (j ≫ p) ↦
    a ≫ G) hl
  simp only [Category.assoc] at hfa hla
  apply sliceUnderUncurry_injective (coconeVertexDiagram d)
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeRootBaseEdgeFamily,
    normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp]
  change joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
      (joinMap tetrahedronRootEdge (𝟙 T) ≫ (sliceUnderUncurry F ≫ Q)) = _
  calc
    _ = joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫
        (sliceUnderUncurry C ≫ Q) := by
      rw [← Category.assoc, ← joinMap_comp, Category.comp_id,
        tetrahedronRootEdge_target_terminalFace, hjoin]
      simp only [Category.assoc, hfa]
    _ = joinMap (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫
        (sliceUnderUncurry R ≫ G) := congrArg (fun k ↦ _ ≫ k) hC
    _ = joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ (sliceUnderUncurry L ≫ G) := by
      rw [triangleTip_longEdge, hjoin]
      simp only [Category.assoc, hla]
    _ = _ := htip

end
end SerrePositivity.InfinityCategories.HomotopyLimits
