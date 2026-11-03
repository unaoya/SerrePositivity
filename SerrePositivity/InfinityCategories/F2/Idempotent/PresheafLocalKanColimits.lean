module

public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite

/-!
概要：持ち上げた元の射の全局所左 Kan 図式は、元の前層圏で余極限を持つ。
方針：元の小さい局所添字の ULift との同型で、証明済みの前層余極限を移す。
規約：元の全局所図式を保持し、大きい任意の余極限の存在を仮定しない。
使われ方：HTT 5.1.4.8 の元の Yoneda 後合成の左 Kan 延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の射を持ち上げた全局所左 Kan 添字上の前層図式は、同じ全図式の余極限を持つ。 -/
lemma presheafLocalKanDiagram_hasColimit {K C E : SSet.{u}} (δ : K ⟶ C)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ PresheafInfinity E)
    (c : ((SSet.uliftFunctor.{u + 1, u}).obj C) _⦋0⦌) :
    HasColimit (leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map δ) F₀ c) := by
  obtain ⟨c⟩ := c
  exact (F1B.kanHasColimit_iff_restrict_of_isIso _
    (leftKanShapeUniverseIso.{u, u + 1} δ c).hom).mpr (presheafInfinity_hasColimit _)

end SerrePositivity.InfinityCategories.F2.Idempotent
