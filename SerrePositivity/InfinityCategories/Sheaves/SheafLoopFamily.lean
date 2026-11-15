module

public import SerrePositivity.InfinityCategories.Sheaves.SheafLoopCorners
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FullSubcomplexLoopReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluationPostcomp

/-!
概要：周囲の同じ全 loop 族を層圏へ持ち上げ、終点と loop 同値を保つ。
方針：四つの角の層条件を内部 Hom の既存同型に入れ、loop 条件を包含から反映する。
使われ方：HA §1.1.3、Kerodon §7.1（Tag 02H1）の安定な全部分圏。
規約：持ち上げの包含後の写像を等号で固定する。対象ごとの新しい loop は選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
variable [HasFiniteLimits E]

/-- 周囲の同じ全四角形の族を、四角形の各角の層条件で層圏へ持ち上げる。 -/
def sheafLoopSquareFamily (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    SheafCat J E ⟶ (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (SheafCat J E) :=
  fullSubcomplexLift
    (FunctorVertexSatisfies ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) (PresheafCat C E) (sheafProperty J))
    (sheafAmbientLoopFamily J s ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)
    (sheafAmbientLoopFamily_vertices J hE s hs hΩ) ≫
      fullSubcomplexInternalHomBackward _ _ (sheafProperty J)

/-- 元の層の包含後では、持ち上げた四角形の全族は周囲の同じ全族と等しい。 -/
lemma sheafLoopSquareFamily_comp (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    sheafLoopSquareFamily J hE s hs hΩ ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map (sheafInclusion J) =
    sheafAmbientLoopFamily J s ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι := by
  let l := fullSubcomplexLift
    (FunctorVertexSatisfies ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) (PresheafCat C E) (sheafProperty J))
    (sheafAmbientLoopFamily J s ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)
    (sheafAmbientLoopFamily_vertices J hE s hs hΩ)
  have hb : fullSubcomplexInternalHomBackward
      ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) (PresheafCat C E) (sheafProperty J) ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map (sheafInclusion J) =
    (fullSubcomplexOnVertices _
      (FunctorVertexSatisfies ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])
        (PresheafCat C E) (sheafProperty J))).ι :=
    fullSubcomplexInternalHomBackward_ι _ _ _
  change (l ≫ fullSubcomplexInternalHomBackward _ _ (sheafProperty J)) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f ↦ l ≫ f) hb).trans (fullSubcomplexLift_ι _ _ _))

/-- 元の層の四角形の族は、包含から loop 条件を反映して全 loop 族になる。 -/
def sheafLoopSection (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    SheafCat J E ⟶ loopDiagrams (SheafCat J E) :=
  fullSubcomplexLift IsLoopDiagramVertex (sheafLoopSquareFamily J hE s hs hΩ) (by
    intro x
    apply isLoopDiagramVertex_of_fullSubcomplex (sheafProperty (E := E) J)
    have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
      (sheafLoopSquareFamily_comp J hE s hs hΩ)
    exact (congrArg IsLoopDiagramVertex h).mpr
      (fullSubcomplexOnVertices_vertex ((sheafAmbientLoopFamily J s).app _ x)))

/-- loop 条件を忘れる包含後の全族は、同じ持ち上げた四角形の族である。 -/
lemma sheafLoopSection_comp (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    sheafLoopSection J hE s hs hΩ ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι =
      sheafLoopSquareFamily J hE s hs hΩ :=
  fullSubcomplexLift_ι _ _ _

/-- 層の包含を通した全角評価は、周囲の元の loop 族の同じ角の評価。 -/
lemma sheafLoopSection_evaluation (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) (i j : Fin 2) :
    (sheafLoopSection J hE s hs hΩ ≫ loopDiagramEvaluation (SheafCat J E) i j) ≫
      sheafInclusion J = sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) i j := by
  calc
    _ = (sheafLoopSquareFamily J hE s hs hΩ ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) ≫
        sheafInclusion J := by
      dsimp only [loopDiagramEvaluation]
      simp only [← Category.assoc, sheafLoopSection_comp]
    _ = (sheafLoopSquareFamily J hE s hs hΩ ≫
        (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map (sheafInclusion J)) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) := by
      rw [Category.assoc, ← evaluateFunctorAt_postcomp, ← Category.assoc]
    _ = _ := by
      rw [sheafLoopSquareFamily_comp, Category.assoc]
      rfl

/-- 持ち上げた同じ loop 族の終点は、層圏の恒等写像と厳密に等しい。 -/
lemma sheafLoopSection_target (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    sheafLoopSection J hE s hs hΩ ≫ loopDiagramEvaluation (SheafCat J E) 1 1 =
      𝟙 (SheafCat J E) := by
  haveI : Mono (sheafInclusion (E := E) J) := by
    dsimp only [sheafInclusion]
    infer_instance
  apply (cancel_mono (sheafInclusion (E := E) J)).mp
  rw [sheafLoopSection_evaluation, (sheafAmbientLoopFamily_target J s hs), Category.id_comp]

/-- 持ち上げた同じ loop 関手は、係数の指定 loop 同値の全後合成と厳密に等しい。 -/
lemma sheafLoopSection_source (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    sheafLoopSection J hE s hs hΩ ≫ loopDiagramEvaluation (SheafCat J E) 0 0 =
      postcomposeSheafFunctor J hΩ.choose := by
  haveI : Mono (sheafInclusion (E := E) J) := by
    dsimp only [sheafInclusion]
    infer_instance
  apply (cancel_mono (sheafInclusion (E := E) J)).mp
  rw [sheafLoopSection_evaluation, sheafAmbientLoopFamily_evaluation, postcomposeSheafFunctor_comp]
  rfl

/-- 持ち上げた元の全 loop 関手は層圏の同値である。 -/
lemma sheafLoopSection_loop_isQCatEquivalence (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0)) :
    IsQCatEquivalence
      (sheafLoopSection J hE s hs hΩ ≫ loopDiagramEvaluation (SheafCat J E) 0 0) := by
  rw [sheafLoopSection_source]
  exact postcomposeSheafFunctor_isQCatEquivalence J hΩ.choose

end SerrePositivity.InfinityCategories.Sheaves
