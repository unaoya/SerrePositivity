module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.PosetSubtypeNerveInclusion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetTerminalExtension

/-!
概要：順序部分型の図式を元の順序集合へ厳密に延長する。
方針：全部分複体の同型と、有限局所余極限・指定終対象への延長を接続する。
規約：元の図式と指定した終対象を保持する。使われ方：一般安定性判定の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma exists_finitePosetSubtypeLeftKan_strict_extension {P : Type u} [PartialOrder P]
    [Finite P] (T : P → Prop) {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X]
    (G : nerve {p : P // T p} ⟶ X) :
    ∃ F : nerve P ⟶ X, nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) ≫ F = G ∧
      ∀ c : (nerve P) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) F c) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_finitePosetLeftKan_strict_extension (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.posetSubtypeInclusion_nerveMap_isFullyFaithful T) G

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma exists_posetSubtype_downward_terminal_extension {P : Type u} [PartialOrder P]
    (T : P → Prop) (hT : ∀ {a b : P}, a ≤ b → T b → T a) {X : SSet.{u}}
    (G : nerve {p : P // T p} ⟶ X) (z : X _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    ∃ F : nerve P ⟶ X, nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) ≫ F = G ∧
      ∀ v, ¬ T (nerveEquiv v) → F.app (Opposite.op ⦋0⦌) v = z := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso T
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_poset_downward_terminal_extension T hT (e.inv ≫ G) z hz
  refine ⟨F, ?_, hv⟩
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι T, Category.assoc, hF]
  exact e.hom_inv_id_assoc G

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
