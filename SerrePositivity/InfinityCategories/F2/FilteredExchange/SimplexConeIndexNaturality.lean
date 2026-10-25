module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplexConeParameter
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RightConeCoefficientNaturality

/-!
概要：全係数付きの標準単体錐は、追加した終点を固定する全添字制限に自然。
方針：標準 join 座標と実錐への係数追加の自然性を使う。
規約：元の全面を保持。使われ方：実四面体の三つの残る面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の標準単体錐は、同じ終点固定添字制限で実全面を保つ。 -/
lemma simplexConeParameter_index_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (P : SSet.{u}) :
    (stdSimplex.map (PinchedHom.extend α) ▷ P) ≫ simplexConeParameter n P =
      simplexConeParameter m P ≫ joinMap (stdSimplex.map α ▷ P) (𝟙 Δ[0]) := by
  have hs : (stdSimplex.map (PinchedHom.extend α) ▷ P) ≫ (β_ Δ[n + 1] P).hom =
      (β_ Δ[m + 1] P).hom ≫ (P ◁ stdSimplex.map (PinchedHom.extend α)) := by
    apply SSet.hom_ext
    intro d
    rfl
  have hi : stdSimplex.map (PinchedHom.extend α) ≫ (joinStdSimplexIso n 0).inv =
      (joinStdSimplexIso m 0).inv ≫ joinMap (stdSimplex.map α) (𝟙 Δ[0]) := by
    have h := congrArg (fun k => (joinStdSimplexIso m 0).inv ≫ k ≫
      (joinStdSimplexIso n 0).inv) (joinStdSimplexIso_rightPoint_naturality α)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using h.symm
  change (stdSimplex.map (PinchedHom.extend α) ▷ P) ≫
      (β_ Δ[n + 1] P).hom ≫ (P ◁ (joinStdSimplexIso n 0).inv) ≫
        rightConeCoefficient Δ[n] P = _
  rw [← Category.assoc, hs, Category.assoc, ← whiskerLeft_comp_assoc, hi,
    whiskerLeft_comp, Category.assoc, rightConeCoefficient_naturality]
  rfl

end SerrePositivity.InfinityCategories.F2
