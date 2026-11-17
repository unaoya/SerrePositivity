module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowDegeneracies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingCocone
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
概要：退化した元の基底射列を、真に低い次数の非退化射列からの全射表示にする。
方針：既存の非退化表示を用い、同次数の全射が恒等射であることから次数の狭義不等式を得る。
規約：係数や基底射列を選び直す同値ではなく、元の射列の表示の等式。
使われ方：IS-W2 R03f.2のlatchingの余極限性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial
variable {I : Type u} [SmallCategory I]

/-- 退化した基底射列は、真に低い次数の同じ非退化表示を持つ。 -/
theorem simplicialReplacement_degenerate_presentation {n : ℕ}
    (σ : ComposableArrows I n) (hσ : σ ∈ (nerve I).degenerate n) :
    ∃ (m : ℕ) (_ : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi α)
      (τ : (nerve I).nonDegenerate m), σ = (nerve I).map α.op τ := by
  obtain ⟨m, α, hα, τ, h⟩ := (nerve I).exists_nonDegenerate σ
  haveI : Epi α := hα
  refine ⟨m, ?_, α, hα, τ, h⟩
  by_contra hlt
  have hmn : m = n := le_antisymm (SimplexCategory.le_of_epi α) (Nat.le_of_not_gt hlt)
  subst m
  rw [SimplexCategory.eq_id_of_epi α, op_id, (nerve I).map_id] at h
  change σ = τ.val at h
  exact τ.property (h ▸ hσ)

/-- 真に次数を下げる同じ全射を、元の外側latchingの対象にする。 -/
def simplicialReplacementLatchingIndexOfEpi {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] : LatchingIndex simplexOp (Opposite.op ⦋n⦌) :=
  ⟨Over.mk α.op, (by change Epi α; infer_instance), (by
    intro h
    exact (Nat.ne_of_lt hm) (congrArg (fun q : SimplexCategoryᵒᵖ => q.unop.len)
      (identities_endpoints α.op h)))⟩

/-- このlatching対象の脚は、元の同じ全射の反対射そのもの。 -/
theorem simplicialReplacementLatchingIndexOfEpi_hom {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] :
    (simplicialReplacementLatchingIndexOfEpi hm α).obj.hom = α.op := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
