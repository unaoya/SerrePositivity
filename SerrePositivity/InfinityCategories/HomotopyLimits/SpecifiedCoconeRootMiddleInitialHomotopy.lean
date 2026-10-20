module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEndInitialHomotopy
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalInitialFaces

/-!
概要：中央の初期端面比較を、左右と同じ固定終点の初期 Hom 空間へ戻す。
方針：同じ raw な円柱を fiber に持ち上げ、評価と底の全時刻固定を回収する。
規約：元の二つの端面族を保持する。使われ方：三比較の合成と共通 end の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder (f ≫ (i ≫ p)))) c
local notation "Q" => sliceUnderProjection v ≫ q
local notation "H" => specifiedCoconeRootVerticalInitialFaceComparison hp p c hc dB dC y
local notation "A₀" => specifiedCoconeRootStartInitialFamily hp p c hc dB dC y
local notation "A₁" => specifiedCoconeRootEndInitialFamily hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 同じ初期端面比較の全族は、同じ固定終点の fiber に入る。 -/
lemma specifiedCoconeRootMiddleInitialHomotopy_fixed : (H).h ≫ Q = SSet.const y := by
  rw [specifiedCoconeRootVerticalInitialFaceComparison_raw]
  simpa only [Category.assoc] using
    (specifiedCoconeRootVerticalInitialComparison_fixed hp p c hc dB dC y)

/-- 元の二端面の初期 Hom 族を、同じ中央比較円柱で結ぶ。 -/
def specifiedCoconeRootMiddleInitialHomotopy : SSet.Homotopy A₀ A₁ where
  h := vertexFiberLift Q y (H).h (specifiedCoconeRootMiddleInitialHomotopy_fixed hp p c hc dB dC y)
  h₀ := by
    change SSet.ι₀ ≫ vertexFiberLift Q y (H).h _ = A₀
    apply vertexFiber_hom_ext Q y
    rw [Category.assoc, vertexFiberLift_ι, (H).h₀,
      specifiedCoconeRootStartInitialFamily, initialDiagramHomFamily, vertexFiberLift_ι]
  h₁ := by
    change SSet.ι₁ ≫ vertexFiberLift Q y (H).h _ = A₁
    apply vertexFiber_hom_ext Q y
    rw [Category.assoc, vertexFiberLift_ι, (H).h₁,
      specifiedCoconeRootEndInitialFamily, initialDiagramHomFamily, vertexFiberLift_ι]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 包含後は元の中央比較円柱の raw な射そのもの。 -/
lemma specifiedCoconeRootMiddleInitialHomotopy_ι :
    (specifiedCoconeRootMiddleInitialHomotopy hp p c hc dB dC y).h ≫ vertexFiberι Q y =
      (H).h := by
  rw [specifiedCoconeRootMiddleInitialHomotopy, vertexFiberLift_ι]

/-- 同じ中央比較は、元の共通部分の可変終点の全族を全時刻固定する。 -/
lemma specifiedCoconeRootMiddleInitialHomotopy_evaluation :
    (specifiedCoconeRootMiddleInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ specifiedCoconeCommonHomFamily hp p c hc dB dC y := by
  apply vertexFiber_hom_ext q y
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
    ← Category.assoc (specifiedCoconeRootMiddleInitialHomotopy hp p c hc dB dC y).h
      (vertexFiberι Q y) (sliceUnderProjection v),
    specifiedCoconeRootMiddleInitialHomotopy_ι]
  change (specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
    sliceUnderProjection v = _
  rw [specifiedCoconeRootVerticalInitialComparison_projection, Category.assoc,
    specifiedCoconeRootVerticalInitialFamily_projection,
    specifiedCoconeLeftRootedHomFamily_endpoint]

/-- 同じ中央比較は、元の時間零の初期 Hom の底も全時刻固定する。 -/
lemma specifiedCoconeRootMiddleInitialHomotopy_base :
    (specifiedCoconeRootMiddleInitialHomotopy hp p c hc dB dC y).h ≫
        leftFibrationInitialProjection q c y = fst T Δ[1] ≫ A₀ ≫
          leftFibrationInitialProjection q c y := by
  apply vertexFiber_hom_ext (sliceUnderProjection (v ≫ q)) y
  simp only [Category.assoc, leftFibrationInitialProjection, vertexFiberMap_ι]
  rw [← Category.assoc _ (vertexFiberι Q y) (sliceUnderPostcomp v q),
    specifiedCoconeRootMiddleInitialHomotopy_ι,
    specifiedCoconeRootVerticalInitialFaceComparison_base]
  have hA₀ : A₀ ≫ vertexFiberι Q y =
      specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y ≫
        normalizedCoconeRestriction
          (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 2)) (specifiedCoconeRootClosingLeft_initial hp p c hc dB dC) := by
    rw [specifiedCoconeRootStartInitialFamily, initialDiagramHomFamily, vertexFiberLift_ι]
  rw [← Category.assoc A₀ (vertexFiberι Q y) (sliceUnderPostcomp v q), hA₀]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
