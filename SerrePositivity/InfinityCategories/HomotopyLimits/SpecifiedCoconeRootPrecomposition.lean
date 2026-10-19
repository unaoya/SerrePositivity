module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEdgeFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedEdgeFamilyHomotopy

/-!
概要：指定余錐の全 Hom の族の共通成分を、元の native な共通脚による前合成と比較する。
方針：辺 03 の始点・終点の厳密な係数公式に、終点を保つ切断との比較を適用する。
規約：元の指定余錐の余極限性は仮定しない。重み付き end の整合性は後続の証明課題。
使われ方：共通 path end 内の比較の共通成分。
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

/-- 固定終点の共通脚の終点制限は、元の全 Hom の標準点図式による表示そのもの。 -/
lemma specifiedCoconeRootBaseEdgeFiberFamily_target :
    specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y ≫
        normalizedCoconeRestrictionFiber (specifiedCoconeNativeRootEdge hp p c hc dB dC)
          (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) y =
      (leftFibrationInitialBaseIso (sliceUnderProjection p)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) y).inv := by
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
        (stdSimplex.δ (0 : Fin 2)) (specifiedCoconeNativeRootEdge_target hp p c hc dB dC)) hι
  simpa only [Category.assoc, specifiedCoconeRootBaseEdgeFiberFamily] using
    h.trans (specifiedCoconeRootBaseEdgeFamily_target hp p c hc dB dC y)

/-- 同じ指定余錐の頂点の Hom で表示した、元の native な共通脚の実際の前合成。 -/
def specifiedCoconeNativeRootHomPrecomposition :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      pinchedHomLeft c.vertex y :=
  (leftFibrationInitialBaseIso (sliceUnderProjection p)
    (partialColimitSpecifiedPathCocone hp p c hc dB dC) y).inv ≫
    cosliceEdgeFiberPrecomposition (specifiedCoconeNativeRootEdge hp p c hc dB dC)
      (coconeVertexDiagram c)
      (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))
      (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)
      (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) y ≫
    (leftFibrationInitialBaseIso (sliceUnderProjection (f ≫ (i ≫ p))) c y).hom

/-- 四面体から得た共通成分は、元の native な共通脚の前合成と全 Hom パラメータでホモトピック。 -/
lemma specifiedCoconeRootedHomFamily_precomposition_homotopy :
    Nonempty (SSet.Homotopy
      (specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y ≫
        leftFibrationInitialProjection (sliceUnderProjection (f ≫ (i ≫ p))) c y ≫
          (leftFibrationInitialBaseIso (sliceUnderProjection (f ≫ (i ≫ p))) c y).hom)
      (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y)) := by
  obtain ⟨H⟩ := cosliceEdgeFamily_precomposition_homotopy
    (specifiedCoconeNativeRootEdge hp p c hc dB dC) y
    (specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y)
    (coconeVertexDiagram c)
    (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))
    (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)
    (specifiedCoconeNativeRootEdge_target hp p c hc dB dC)
  exact ⟨by simpa only [specifiedCoconeRootBaseEdgeFiberFamily_source,
      specifiedCoconeRootBaseEdgeFiberFamily_target, specifiedCoconeNativeRootHomPrecomposition,
      Category.assoc] using
    (functorHomotopyPostcomp H
      (leftFibrationInitialBaseIso (sliceUnderProjection (f ≫ (i ≫ p))) c y).hom)⟩

/-- 指定余錐の全 Hom の族の共通部分の比較は、元の native な共通脚の前合成にホモトピック。 -/
lemma specifiedCoconeCommonHomFamily_rootPrecomposition_homotopy :
    Nonempty (SSet.Homotopy
      (specifiedCoconeCommonHomFamily hp p c hc dB dC y ≫ coconeMappingSpaceHomComparison c hc y)
      (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y)) := by
  obtain ⟨H₀⟩ := specifiedCoconeRootedHomComparison_homotopy hp p c hc dB dC y
  obtain ⟨H₁⟩ := specifiedCoconeRootedHomFamily_precomposition_homotopy hp p c hc dB dC y
  exact ⟨FunctorIso.simplicialHomotopy ((functorIsoOfSimplicialHomotopy H₀) ≪≫
    (functorIsoOfSimplicialHomotopy H₁))⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
