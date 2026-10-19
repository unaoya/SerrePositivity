module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftHomTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomEdgeTip

/-!
概要：指定余錐の全 Hom の左三角形族を、元の native な共通脚の余錐族へ制限する。
方針：長辺 02 とその両端の座標を使い、始対象の中間 Hom と元の全 Hom パラメータを計算する。
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
/-- 三角形の長辺の始点は、第一辺の始点そのもの。 -/
lemma triangleLongEdge_sourceVertex :
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) : (Δ[0] : SSet.{u}) ⟶ Δ[2]) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)

/-- 同じ左三角形の底の長辺は、元の native な共通脚そのもの。 -/
lemma specifiedCoconeLeftRootDiagram_rootEdge :
    stdSimplex.δ (1 : Fin 3) ≫
        (specifiedCoconeLeftRootedTriangle hp p c hc dB dC ≫
          sliceUnderProjection (f ≫ (i ≫ p))) =
      specifiedCoconeNativeRootEdge hp p c hc dB dC :=
  (Category.assoc _ _ _).symm.trans
    (specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC)

/-- 全 Hom の左三角形族の底を、元の native な共通脚そのものの上へ制限した族。 -/
def specifiedCoconeLeftRootBaseEdgeFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder (specifiedCoconeNativeRootEdge hp p c hc dB dC) :=
  (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
    sliceUnderPostcomp (specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
      (sliceUnderProjection (f ≫ (i ≫ p)))) ≫
    normalizedCoconeRestriction
      (specifiedCoconeLeftRootedTriangle hp p c hc dB dC ≫
        sliceUnderProjection (f ≫ (i ≫ p))) (stdSimplex.δ (1 : Fin 3))
      (specifiedCoconeLeftRootDiagram_rootEdge hp p c hc dB dC)

/-- 共通脚上の全 Hom の族は、元の終点 y を保つ。 -/
lemma specifiedCoconeLeftRootBaseEdgeFamily_fixed :
    specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y ≫
      sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC) = SSet.const y := by
  simpa only [specifiedCoconeLeftRootBaseEdgeFamily, Category.assoc,
    normalizedCoconeRestriction_projection, sliceUnderPostcomp_projection] using
    (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)

/-- 元の共通脚の辺全体の固定終点余錐空間に属する全 Hom の族。 -/
def specifiedCoconeLeftRootBaseEdgeFiberFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      coconeMappingSpace (specifiedCoconeNativeRootEdge hp p c hc dB dC) y :=
  vertexFiberLift _ y (specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootBaseEdgeFamily_fixed hp p c hc dB dC y)

/-- 共通脚の始点制限は、同じ左三角形から得た始対象の中間 Hom の底を厳密に回収する。 -/
lemma specifiedCoconeLeftRootBaseEdgeFamily_source :
    specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) =
      specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
          vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y := by
  have h := initialDiagramHomFamily_base (sliceUnderProjection (f ≫ (i ≫ p))) c
    (specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    (specifiedCoconeLeftRootedTriangle_initial hp p c hc dB dC) y
    (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)
  have h' : specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
      leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
        vertexFiberι (sliceUnderProjection (coconeVertexDiagram c)) y = _ := h
  refine Eq.trans ?_ h'.symm
  apply sliceUnderUncurry_injective (coconeVertexDiagram c)
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeLeftRootBaseEdgeFamily,
    normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    ← Category.assoc, ← joinMap_comp, Category.comp_id, triangleLongEdge_sourceVertex]

/-- 固定終点の共通脚の始点制限も、同じ中間 Hom の射影そのもの。 -/
lemma specifiedCoconeLeftRootBaseEdgeFiberFamily_source :
    specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y =
      specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y := by
  apply vertexFiber_hom_ext
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  have hι := vertexFiberLift_ι
    (sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC)) y
    (specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootBaseEdgeFamily_fixed hp p c hc dB dC y)
  have h := congrArg (fun a :
      pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
        sliceUnder (specifiedCoconeNativeRootEdge hp p c hc dB dC) ↦
      a ≫ normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)) hι
  simpa only [Category.assoc, specifiedCoconeLeftRootBaseEdgeFiberFamily] using
    h.trans (specifiedCoconeLeftRootBaseEdgeFamily_source hp p c hc dB dC y)

/-- 共通脚の終点制限は、元の指定余錐の同じ全 Hom の底のパラメータ。 -/
lemma specifiedCoconeLeftRootBaseEdgeFamily_target :
    specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y ≫
        normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) =
      (leftFibrationInitialBaseIso (sliceUnderProjection p)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) y).inv ≫
        vertexFiberι (sliceUnderProjection
          (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))) y := by
  let d := partialColimitSpecifiedPathCocone hp p c hc dB dC
  let T := pinchedHomLeft d.vertex y
  let Q := sliceUnderProjection (f ≫ (i ≫ p))
  let G := sliceUnderProjection (i ≫ p)
  let F := specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
  let C := specifiedCoconeLeftCommonEdgeFamily hp p c hc dB dC y
  let L := specifiedCoconeLeftFullHomFamily hp p c hc dB dC y
  have hf : joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 T) ≫ sliceUnderUncurry F =
      sliceUnderUncurry C := by
    have h := congrArg sliceUnderUncurry
      (specifiedCoconeLeftRootedHomFamily_terminal hp p c hc dB dC y)
    rw [sliceUnderUncurry_restrict, specifiedCoconeLeftTerminalHomFamily,
      sliceUnderUncurry_eqToHom
        (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC).symm] at h
    exact h
  have hC : sliceUnderUncurry C ≫ Q = sliceUnderUncurry L ≫ G := by
    dsimp only [C, Q, L, G]
    rw [specifiedCoconeLeftCommonEdgeFamily, sliceUnderUncurry_postcomp,
      Category.assoc, sliceUnderRestrict_projection]
  have htip := pointRestrictionFullEdgeFamily_tip_uncurry (c := dB)
    (sliceUnderProjection p) (sliceUnderProjection (i ≫ p)) (sliceUnderRestrict p i)
    (sliceUnderRestrict_projection p i) d
    (specifiedCoconeLeftTransportEdge hp p c hc dB dC) y
  have hjoin {K L M : SSet.{u + 1}} (a : K ⟶ L) (b : L ⟶ M) :
      joinMap (a ≫ b) (𝟙 T) = joinMap a (𝟙 T) ≫ joinMap b (𝟙 T) := by
    simpa only [Category.comp_id] using joinMap_comp a b (𝟙 T) (𝟙 T)
  have hfa := congrArg (fun a : join (Δ[1] : SSet.{u + 1}) T ⟶ sliceUnder (f ≫ (i ≫ p)) ↦
    a ≫ Q) hf
  simp only [Category.assoc] at hfa
  apply sliceUnderUncurry_injective (coconeVertexDiagram d)
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeLeftRootBaseEdgeFamily,
    normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp]
  change joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫
      (joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 T) ≫ (sliceUnderUncurry F ≫ Q)) = _
  calc
    _ = joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ (sliceUnderUncurry C ≫ Q) := by
      rw [← Category.assoc, ← joinMap_comp, Category.comp_id, ← triangleTip_longEdge, hjoin]
      simp only [Category.assoc, hfa]
    _ = joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ (sliceUnderUncurry L ≫ G) :=
      congrArg (fun k ↦ _ ≫ k) hC
    _ = _ := htip

/-- 固定終点の共通脚の終点制限も、元の全 Hom の点図式の表示そのもの。 -/
lemma specifiedCoconeLeftRootBaseEdgeFiberFamily_target :
    specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) y =
      (leftFibrationInitialBaseIso (sliceUnderProjection p)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) y).inv := by
  apply vertexFiber_hom_ext
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  have hι := vertexFiberLift_ι
    (sliceUnderProjection (specifiedCoconeNativeRootEdge hp p c hc dB dC)) y
    (specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootBaseEdgeFamily_fixed hp p c hc dB dC y)
  have h := congrArg (fun a :
      pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
        sliceUnder (specifiedCoconeNativeRootEdge hp p c hc dB dC) ↦
      a ≫ normalizedCoconeRestriction (specifiedCoconeNativeRootEdge hp p c hc dB dC)
        (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC)) hι
  simpa only [Category.assoc, specifiedCoconeLeftRootBaseEdgeFiberFamily] using
    h.trans (specifiedCoconeLeftRootBaseEdgeFamily_target hp p c hc dB dC y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
