module
public import SerrePositivity.InfinityCategories.Stable.LoopSquarePushoutOfEquivalence

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma isSuspensionDiagramVertex_of_isLoop_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌)
    (hv : IsLoopDiagramVertex v) : IsSuspensionDiagramVertex v := by
  let t : LoopSquare (squareVertex (squareDiagram v) 1 1) :=
    { square := squareDiagram v
      zero_corner := hv.1
      target_eq := rfl
      other_zero := hv.2.1
      isPullback := hv.2.2 }
  exact ⟨hv.1, hv.2.1, t.isPushout_of_loopEquivalence s hs hΩ⟩

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def loopToSuspensionDiagramsOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    loopDiagrams X ⟶ suspensionDiagrams X :=
  fullSubcomplexLift IsSuspensionDiagramVertex
    (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι (fun v ↦
      isSuspensionDiagramVertex_of_isLoop_of_loopEquivalence s hs hΩ v.val
        (fullSubcomplexOnVertices_vertex v))

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma loopToSuspensionDiagramsOfLoopEquivalence_ι {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    loopToSuspensionDiagramsOfLoopEquivalence s hs hΩ ≫
      (fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι =
    (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι :=
  fullSubcomplexLift_ι _ _ _

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma loopToSuspensionDiagramsOfLoopEquivalence_evaluation {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (i j : Fin 2) :
    loopToSuspensionDiagramsOfLoopEquivalence s hs hΩ ≫
      suspensionDiagramEvaluation X i j = loopDiagramEvaluation X i j := by
  dsimp only [suspensionDiagramEvaluation, loopDiagramEvaluation]
  rw [← Category.assoc, loopToSuspensionDiagramsOfLoopEquivalence_ι]

end SerrePositivity.InfinityCategories
