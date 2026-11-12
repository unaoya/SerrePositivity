module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.RelativeInitialVertices
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
概要：指定した図式の族の各頂点に相対始対象があれば、その族に沿う普遍な持ち上げは存在する。
方針：相対始対象全体からの射を引き戻し、正次元の充填と頂点での存在を合わせる。
規約：quasicategory 性や元の射の fibration 性は不要。
使われ方：Kan 拡張の存在仮定を対象の図式の点ごとの余極限へ弱める。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対始対象全体からの射の引き戻しは、各頂点で存在すれば自明 Kan fibration。
方針：正次元の境界充填は底変換で移し、零次元は指定された相対始対象から作る。
規約：存在は図式 b の像の頂点だけについて要求する。
使われ方：特定の図式の族に沿う coherent な普遍余錐の選択。 -/
lemma kanRelativeInitialPullback_trivialKanFibration {E F A : SSet.{u}}
    (p : E ⟶ F) (b : A ⟶ F)
    (hex : ∀ a : A _⦋0⦌, ∃ e : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) e = b.app (Opposite.op ⦋0⦌) a ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.fst b (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero =>
    constructor
    intro a d sq
    obtain ⟨e, he, hei⟩ := hex (SSet.yonedaEquiv d)
    let e' : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices p : SSet.{u}) _⦋0⦌ := ⟨e, by
      intro v
      have hv : v = 𝟙 _ := Subsingleton.elim _ _
      simpa only [hv, op_id, Functor.map_id_apply] using hei⟩
    have hd : d ≫ b = SSet.yonedaEquiv.symm e' ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact he.symm
    refine CommSq.HasLift.mk' {
      l := pullback.lift d (SSet.yonedaEquiv.symm e') hd
      fac_left := boundary.hom_ext₀
      fac_right := pullback.lift_fst _ _ _ }
  | succ n =>
    have := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection_hasLiftingProperty_boundary p n
    infer_instance

/-- 概要：図式の各頂点で相対始対象が存在すれば、図式全体に相対始対象の族を選べる。
方針：相対始対象全体の引き戻しからの自明 Kan fibration の切断を取る。
規約：像の頂点の外での存在は要求しない。
使われ方：点ごとの余極限からの Kan 拡張の coherent な構成。 -/
lemma exists_kanRelativeInitial_family_of_vertices {E F A : SSet.{u}}
    (p : E ⟶ F) (b : A ⟶ F)
    (hex : ∀ a : A _⦋0⦌, ∃ e : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) e = b.app (Opposite.op ⦋0⦌) a ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p e) :
    ∃ l : A ⟶ E, l ≫ p = b ∧
      ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (l.app (Opposite.op ⦋0⦌) a) := by
  have := kanRelativeInitialPullback_trivialKanFibration p b hex
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (pullback.fst b (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p))
  refine ⟨s ≫ pullback.snd b (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices p).ι, ?_, ?_⟩
  · change s ≫ pullback.snd b (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p = b
    rw [← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
      ((s ≫ pullback.snd b (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection p)).app (Opposite.op ⦋0⦌) a)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
