module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowNormalization

/-!
概要：元のlatching余錐の全ての脚は、同じ退化行を単体ごとに覆う。
方針：元の非退化表示をlatching対象へ戻し、係数を同じ始点の等式で移送する。
規約：基底射列と係数の双方を厳密に回収する。余極限性の一意性は別に検証する。
使われ方：IS-W2 R03f.2の退化行のlatching余極限の検収。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

/-- 同じlatching余錐の脚は、退化行の元の各単体を厳密に回収する。 -/
theorem simplicialReplacementRowLatching_jointly_surjective (q : SimplexCategoryᵒᵖ)
    (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s := by
  rcases s with ⟨⟨σ,x⟩,hσ⟩
  change σ ∈ (nerve I).degenerate n at hσ
  obtain ⟨m, hm, α, hα, τ, h⟩ := simplicialReplacement_degenerate_presentation σ hσ
  haveI : Epi α := hα
  subst σ
  have e : F.obj (τ.val.obj (α.toOrderHom 0)) = F.obj (τ.val.obj 0) :=
    congrArg (fun k => F.obj (τ.val.obj k)) (simplicialReplacement_epi_zero α)
  refine ⟨simplicialReplacementLatchingIndexOfEpi hm α,
    (⟨τ.val, (eqToHom e).app q x⟩ : (simplicialReplacementRow F m).obj q), ?_⟩
  apply Subtype.ext
  refine Sigma.ext (show α.toOrderHom.monotone.functor ⋙ τ.val =
    (nerve I).map α.op τ from rfl) ?_
  apply heq_of_eq
  change (F.map (τ.val.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))).app q
    ((eqToHom e).app q x) = x
  rw [simplicialReplacement_epi_coefficient]
  change ((eqToHom e ≫ eqToHom e.symm).app q) x = x
  rw [eqToHom_trans]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
