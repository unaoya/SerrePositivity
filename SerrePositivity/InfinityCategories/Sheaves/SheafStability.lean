module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Sheaves.SheafLoopFamily

/-!
概要：任意の小さい site と安定な presentable 係数について、層の全部分準圏の安定性を示す。
方針：同じ零頂点と有限極限、持ち上げた全 loop 切断と同値を既存の安定性判定に入れる。
  文献対応：HA §1.1.3、HTT 6.2.2.7。Kerodon §7.1（Tag 02H1）の元の極限錐を使う。
規約：Čech 層の元の定義を使い、hypercompletion や左完全性の追加条件を課さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 安定な presentable 係数の層の元の全部分準圏は安定である。 -/
@[cite HA "1.1.3.2" (partial := special)
  "安定な前層準圏の全部分圏のうち、小さい通常の site の Čech 層の安定性に特殊化する。presentable 係数を仮定する。"]
theorem sheaf_isStable [IsStable E] (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsStable (SheafCat J E) := by
  letI : HasFiniteLimits E := hasFiniteLimits_of_isStable E
  letI : HasFiniteLimits (SheafCat J E) := sheaf_hasFiniteLimits J hE
  letI : HasZeroVertex (SheafCat J E) := sheaf_hasZeroVertex J hE
  let s := Classical.choose (trivialKanFibration_exists_section (loopDiagramEvaluation E 1 1))
  have hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E :=
    Classical.choose_spec (trivialKanFibration_exists_section (loopDiagramEvaluation E 1 1))
  let e := (suspensionLoopDiagramEquivalence E).symm.trans
    (suspensionDiagramSourceEquivalence E)
  have he : IsQCatEquivalence (loopDiagramEvaluation E 0 0) := e.isQCatEquivalence
  have hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0) :=
    (loopDiagramSection_isQCatEquivalence s hs).comp he
  exact isStable_of_loopEquivalence (sheafLoopSection J hE s hs hΩ)
    (sheafLoopSection_target J hE s hs hΩ) (sheafLoopSection_loop_isQCatEquivalence J hE s hs hΩ)

end SerrePositivity.InfinityCategories.Sheaves
