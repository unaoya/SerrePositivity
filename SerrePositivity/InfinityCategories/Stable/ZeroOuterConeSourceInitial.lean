module
public import SerrePositivity.InfinityCategories.Stable.LoopConeChoiceModel
public import SerrePositivity.InfinityCategories.Stable.ConeInputSourceFiber

/-!
概要：普遍錐の選択を忘れ、全零隅四角形の始対象を得る。
方針：元の実引き戻しの同型と同じ頂点 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定頂点を保つ錐の比較 `zeroOuterConeSourceFiber_hasInitial`。 -/
lemma zeroOuterConeSourceFiber_hasInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ v : (vertexFiber
      (pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
        (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          IsZeroOuterCospanVertex).ι ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X) x)
        _⦋0⦌, IsInitialVertex v := by
  apply coneChoiceForget_apexFiber_hasInitial _ (fun d ↦ HasFiniteLimits.hasLimit d) x
  exact loopConeChoiceFiber_hasInitial s hs hΩ x
end SerrePositivity.InfinityCategories
