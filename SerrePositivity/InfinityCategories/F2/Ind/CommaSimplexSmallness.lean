module

public import SerrePositivity.InfinityCategories.F2.Ind.JoinBoundaryMapSmallness
public import SerrePositivity.InfinityCategories.F2.Ind.CommaFamily
public import SerrePositivity.InfinityCategories.Core.PullbackSimplex

/-!
概要：小さい始域と固定頂点写像の小さい標的の comma は各次数で小さい。
方針：始域単体と両境界を固定した全余錐へ単射で符号化する。
規約：実際の comma の単体を保持。使われ方：図式の小さい表示添字の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の comma の各単体は、始域単体と元の全余錐の小さい符号で決まる。 -/
lemma leftKanShape_obj_small_of_fixedVertexMaps {B Y : SSet.{u + 1}}
    (δ : B ⟶ Y) (x : Y _⦋0⦌) (hY : HasSmallFixedVertexMaps Y)
    (n : SimplexCategoryᵒᵖ) [Small.{u} (B.obj n)] :
    Small.{u} ((leftKanShape δ x).obj n) := by
  rcases n with ⟨⟨n⟩⟩
  let T (b : B _⦋n⦌) :=
    {F : join (Δ[n] : SSet.{u + 1}) Δ[0] ⟶ Y //
      joinInl Δ[n] Δ[0] ≫ F = SSet.yonedaEquiv.symm (δ.app _ b) ∧
      joinInr Δ[n] Δ[0] ≫ F = SSet.yonedaEquiv.symm x}
  haveI (b : B _⦋n⦌) : Small.{u} (T b) :=
    small_joinMaps_fixedBoundary hY _ _
  let code (s : (leftKanShape δ x) _⦋n⦌) : Σ b : B _⦋n⦌, T b :=
    ⟨(pullback.fst δ (sliceOverProjection (SSet.yonedaEquiv.symm x))).app _ s,
      ⟨((pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm x))).app _ s).val, by
        constructor
        · apply SSet.yonedaEquiv.injective
          rw [Equiv.apply_symm_apply]
          exact (ConcreteCategory.congr_hom (NatTrans.congr_app
            (pullback.condition (f := δ)
              (g := sliceOverProjection (SSet.yonedaEquiv.symm x)))
                (Opposite.op ⦋n⦌)) s).symm
        · exact ((pullback.snd δ (sliceOverProjection
            (SSet.yonedaEquiv.symm x))).app _ s).property⟩⟩
  apply small_of_injective (f := code)
  intro s t h
  apply pullbackSimplex_ext δ (sliceOverProjection (SSet.yonedaEquiv.symm x))
  · exact congrArg Sigma.fst h
  · apply Subtype.ext
    exact congrArg (fun z : Σ b : B _⦋n⦌, T b => z.2.val) h

end SerrePositivity.InfinityCategories.F2.Ind
