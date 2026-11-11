module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagramPullback

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma isSuspensionDiagramVertex_iff_isLoop_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex v ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex v := by
  constructor
  · intro hv
    let w : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) _⦋0⦌ := ⟨v, by
      intro a
      have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [ha, op_id, CategoryTheory.Functor.map_id_apply] using hv⟩
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isLoopDiagramVertex_of_isSuspension_of_loopEquivalence s hs hΩ w
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isSuspensionDiagramVertex_of_isLoop_of_loopEquivalence s hs hΩ v

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def suspensionLoopDiagramsIsoOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (Iso.refl _) _ _
    (isSuspensionDiagramVertex_iff_isLoop_of_loopEquivalence s hs hΩ)

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma suspensionLoopDiagramsIsoOfLoopEquivalence_evaluation {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (i j : Fin 2) :
    (suspensionLoopDiagramsIsoOfLoopEquivalence s hs hΩ).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X i j = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X i j := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
