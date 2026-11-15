module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowNormalization

/-!
概要：同じ基底単体の任意の全射表示は、その同じ非退化表示を経由する。
方針：表示された単体も既存の非退化表示へ戻し、次元・単体・全射の一意性を順に使う。
規約：元の二つの表示の等式と全射の合成の等式を保持する。
使われ方：IS-W2 R03f.2のlatching余錐の一意性の検収。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 任意の全射表示は、元の同じ非退化表示からの全射の合成である。 -/
theorem simplicialReplacement_common_nondegenerate_presentation {X : SSet.{u}} {n m k : ℕ}
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : X.nonDegenerate m)
    (β : ⦋n⦌ ⟶ ⦋k⦌) [Epi β] (υ : X.obj (Opposite.op ⦋k⦌))
    (h : X.map α.op τ = X.map β.op υ) :
    ∃ (γ : ⦋k⦌ ⟶ ⦋m⦌) (_ : Epi γ), β ≫ γ = α ∧ X.map γ.op τ = υ := by
  obtain ⟨l, γ, hγ, y, hυ⟩ := X.exists_nonDegenerate υ
  haveI : Epi γ := hγ
  have he : X.map α.op τ = X.map (β ≫ γ).op y := by
    rw [op_comp, X.map_comp]
    change X.map α.op τ = X.map β.op (X.map γ.op y)
    rw [← hυ]
    exact h
  have hl := X.unique_nonDegenerate_dim (X.map α.op τ) α τ rfl (β ≫ γ) y he
  subst l
  have hy := X.unique_nonDegenerate_simplex (X.map α.op τ) α τ rfl (β ≫ γ) y he
  subst y
  exact ⟨γ, hγ, (X.unique_nonDegenerate_map (X.map α.op τ) α τ rfl (β ≫ γ) τ he).symm,
    hυ.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
