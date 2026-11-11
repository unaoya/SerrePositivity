module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetLeftKanShape
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftStrictExistence

/-!
概要：有限順序添字の局所余極限から、元の図式に厳密に等しい左 Kan 拡張を得る。
方針：非退化単体の単射性と左 comma の包含で局所添字の有限性を証明する。
規約：元の図式と native な左 Kan 添字を保持する。使われ方：安定性の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
lemma exists_finitePosetLeftKan_strict_extension {P Q : Type u} [PartialOrder P]
    [PartialOrder Q] [Finite P] {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X]
    (L : P ⥤ Q) [Mono (nerveMap L)] [InnerFibration (nerveMap L)]
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (nerveMap L)) (F₀ : nerve P ⟶ X) :
    ∃ G : nerve Q ⟶ X, nerveMap L ≫ G = F₀ ∧
      ∀ c : (nerve Q) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap L) G c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits (nerveMap L) hL F₀
  intro c
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.finitePosetLeftKanShape_finite_at L c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits.hasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (nerveMap L) F₀ c)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
