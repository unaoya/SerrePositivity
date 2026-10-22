module
public import SerrePositivity.InfinityCategories.Stable.LoopSuspensionDiagramsOfEquivalence
/-!
概要：二つの零角を持つ同じ四角形の双カルテジアン判定。
方針：全 suspension/loop 図式の頂点条件の同値を元の四角形へ戻す。
規約：零角が一つの場合や一般安定性は結論していない。
使われ方：HA 1.4.2.27 の一般安定性判定に必要な普遍四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の二つの零角と同じ実四角形を保持する。 -/
lemma isPullbackSquare_iff_isPushout_of_zeroCorners_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (F : Δ[1] ⊗ Δ[1] ⟶ X) (hz : IsZeroVertex (squareVertex F 0 1))
    (hw : IsZeroVertex (squareVertex F 1 0)) :
    IsPullbackSquare F ↔ IsPushoutSquare F := by
  have h := isSuspensionDiagramVertex_iff_isLoop_of_loopEquivalence s hs hΩ
    (functorVertex F)
  dsimp only [IsSuspensionDiagramVertex, IsLoopDiagramVertex] at h
  rw [squareDiagram_functorVertex] at h
  exact ⟨fun hp ↦ (h.mpr ⟨hz, hw, hp⟩).2.2,
    fun hp ↦ (h.mp ⟨hz, hw, hp⟩).2.2⟩

/-- 元の二つの零角と同じ実四角形を保持する。 -/
lemma SuspensionSquare.isPullback_of_loopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    {x : X _⦋0⦌} (t : SuspensionSquare x) : IsPullbackSquare t.square :=
  (isPullbackSquare_iff_isPushout_of_zeroCorners_of_loopEquivalence s hs hΩ t.square
    t.zero_corner t.other_zero).mpr t.isPushout
end SerrePositivity.InfinityCategories
