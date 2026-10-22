module
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeNerveInclusion
public import SerrePositivity.InfinityCategories.Stable.PosetTerminalExtension

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
namespace SerrePositivity.InfinityCategories

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma exists_finitePosetSubtypeLeftKan_strict_extension {P : Type u} [PartialOrder P]
    [Finite P] (T : P → Prop) {X : SSet.{u}} [Quasicategory X] [HasFiniteColimits X]
    (G : nerve {p : P // T p} ⟶ X) :
    ∃ F : nerve P ⟶ X, nerveMap (posetSubtypeInclusion T) ≫ F = G ∧
      ∀ c : (nerve P) _⦋0⦌,
        IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) F c) :=
  exists_finitePosetLeftKan_strict_extension (posetSubtypeInclusion T)
    (posetSubtypeInclusion_nerveMap_isFullyFaithful T) G

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma exists_posetSubtype_downward_terminal_extension {P : Type u} [PartialOrder P]
    (T : P → Prop) (hT : ∀ {a b : P}, a ≤ b → T b → T a) {X : SSet.{u}}
    (G : nerve {p : P // T p} ⟶ X) (z : X _⦋0⦌) (hz : IsTerminalVertex z) :
    ∃ F : nerve P ⟶ X, nerveMap (posetSubtypeInclusion T) ≫ F = G ∧
      ∀ v, ¬ T (nerveEquiv v) → F.app (Opposite.op ⦋0⦌) v = z := by
  let e := posetSubtypeNerveIso T
  obtain ⟨F, hF, hv⟩ := exists_poset_downward_terminal_extension T hT (e.inv ≫ G) z hz
  refine ⟨F, ?_, hv⟩
  rw [← posetSubtypeNerveIso_hom_ι T, Category.assoc, hF]
  exact e.hom_inv_id_assoc G

end SerrePositivity.InfinityCategories
