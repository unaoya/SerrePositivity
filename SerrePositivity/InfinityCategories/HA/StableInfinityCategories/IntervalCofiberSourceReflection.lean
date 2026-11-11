module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IntervalCofiberComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IntervalSuspensionReflection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationConnecting

/-!
概要：cofiber の区間族の後二成分の可逆性から第一成分の可逆性を反映する。
方針：全区間族を一回回転し、第三成分の可逆性を懸垂図式で反映する。
規約：点ごとの回転の任意選択を自然な族として扱わない。
使われ方：任意の零角の fiber/cofiber 同値の比較辺の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：実 cofiber の区間族で後二成分が可逆なら第一成分も可逆である。
方針：関手圏で同じ loop 入力による回転を構成し、懸垂の終点評価で反映する。
規約：有限余極限や一般安定性を追加仮定にしない。
使われ方：元の零角の極限錐への比較辺を可逆とする。 -/
lemma ZeroTriangle.source_isEquivalencePath_of_middle_target {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom (Δ[1] : SSet.{u})).obj X)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0))
    (h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasZeroVertex_functorCategory (Δ[1] : SSet.{u}) X
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory (Δ[1] : SSet.{u}) X
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberRotationRectangle_of_loopEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection Δ[1] s) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection_target s hs)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSection_loop_isQCatEquivalence s hΩ) t ht
  have hsource : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex r.rotatedZeroTriangle.square 0 0) := by
    rw [r.rotated_source]
    exact h₁
  have hmiddle : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex r.rotatedZeroTriangle.square 1 0) := by
    rw [r.rotated_middle]
    exact h₂
  have htarget := r.rotatedZeroTriangle.target_isEquivalencePath_of_source_middle
    s hs hΩ r.rotated_isCofiber hsource hmiddle
  exact r.suspensionSquare.source_isEquivalencePath_of_target s hs hΩ htarget

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (source_isEquivalencePath_of_middle_target)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
