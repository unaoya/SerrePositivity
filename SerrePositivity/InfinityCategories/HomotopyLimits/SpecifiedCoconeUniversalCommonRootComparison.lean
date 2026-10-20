module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeUniversalCommonRoot
public import SerrePositivity.InfinityCategories.HomotopyLimits.EvaluationFixedHomotopyTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootFamilyTriangle

/-!
概要：元の左右の根辺族から同じ native 普遍根辺族への二円柱と、元の比較の合成則。
方針：元の全族間円柱の二面を保持し、自明 Kan な終端制限の忠実性を使う。
規約：同じ元の根辺比較の類を回収。使われ方：指定経路の比較を共通根辺で貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rt" => specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "R" => normalizedCoconeRestrictionFiber root (stdSimplex.δ (0 : Fin 2)) rt y
local notation "Q" => Iso.inv (leftFibrationInitialBaseIso (sliceUnderProjection p) d y)
local notation "W" => specifiedCoconeUniversalCommonRootFamily hp p c hc dB dC y
local notation "G" => specifiedCoconeRootFamilyComparison hp p c hc dB dC y

/-- 左の同じ全図式比較の根辺面を、厳密に共通する普遍根辺族への比較として保持する。 -/
def specifiedCoconeLeftUniversalCommonRootComparison : SSet.Homotopy
    (specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y) W :=
  homotopyEndpointTransport (specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y)
    rfl (specifiedCoconeLeftUniversalNativeFamily_root hp p c hc dB dC y)

/-- 右の同じ全図式比較の辺03も、同じ共通普遍根辺族への比較として保持する。 -/
def specifiedCoconeRightUniversalCommonRootComparison : SSet.Homotopy
    (specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y) W :=
  homotopyEndpointTransport (specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y)
    rfl (specifiedCoconeRightUniversalNativeFamily_root hp p c hc dB dC y)

/-- 左の表示変更は、元の全図式比較の根辺面の raw な射を変えない。 -/
lemma specifiedCoconeLeftUniversalCommonRootComparison_raw :
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y).h =
      (specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y).h :=
  homotopyEndpointTransport_raw _ _ _

/-- 右の表示変更も、元の全図式比較の辺03の raw な射を変えない。 -/
lemma specifiedCoconeRightUniversalCommonRootComparison_raw :
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y).h =
      (specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y).h :=
  homotopyEndpointTransport_raw _ _ _

/-- 左の共通根辺比較は、元の同じ全 Hom の点図式係数を全時刻固定する。 -/
lemma specifiedCoconeLeftUniversalCommonRootComparison_terminal :
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y).h ≫ R =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeLeftUniversalCommonRootComparison_raw]
  exact specifiedCoconeLeftNativeUniversalRootFace_terminal hp p c hc dB dC y

/-- 右の共通根辺比較も、同じ全 Hom の点図式係数を全時刻固定する。 -/
lemma specifiedCoconeRightUniversalCommonRootComparison_terminal :
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y).h ≫ R =
      fst T Δ[1] ≫ Q := by
  rw [specifiedCoconeRightUniversalCommonRootComparison_raw]
  exact specifiedCoconeRightNativeUniversalRootFace_terminal hp p c hc dB dC y

/-- 既存の根辺族比較も、表示を共通点図式へ揃えると同じ全時刻固定係数を持つ。 -/
lemma specifiedCoconeRootFamilyComparison_normalized_terminal :
    (G).h ≫ R = fst T Δ[1] ≫ Q := by
  rw [normalizedCoconeRestrictionFiber_eq]
  rw [← Category.assoc, specifiedCoconeRootFamilyComparison_target]
  simpa only [Category.assoc, normalizedCoconeRestrictionFiber_eq] using
    congrArg (fst T Δ[1] ≫ ·)
      (specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y)

/-- 元の左右比較と右の共通根辺比較の合成は、左の同じ比較の類そのものである。 -/
lemma specifiedCoconeUniversalCommonRoot_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy G) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y)) := by
  have := normalizedCoconeRestrictionFiber_of_rightAnodyne root (stdSimplex.δ (0 : Fin 2))
    endpointInclusion_rightAnodyne (coconeVertexDiagram d) rt y
  exact evaluationFixedHomotopyTriangle_homMk_comp R G
    (specifiedCoconeRightUniversalCommonRootComparison hp p c hc dB dC y)
    (specifiedCoconeLeftUniversalCommonRootComparison hp p c hc dB dC y) Q
    (specifiedCoconeRootFamilyComparison_normalized_terminal hp p c hc dB dC y)
    (specifiedCoconeRightUniversalCommonRootComparison_terminal hp p c hc dB dC y)
    (specifiedCoconeLeftUniversalCommonRootComparison_terminal hp p c hc dB dC y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
