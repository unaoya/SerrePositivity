module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionSquare
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionDiagonalCut
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：coherent 合成四角形の全単体での評価を、同じ合成単体の切断として表示する。
方針：slice の curry・uncurry と右 join prism の評価式を組み合わせる。
規約：二つの時間と二つの Hom の単体を全て保持する。
使われ方：対角を元の豊穣合成の標準区間比較と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ slice の族を単体で評価することと、元の join 図式の制限は一致する。 -/
lemma sliceOverUncurry_simplex_coordinate {A K X : SSet.{u}} {p : K ⟶ X}
    (W : A ⟶ sliceOver p) {n : ℕ} (a : A _⦋n⦌) :
    joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ sliceOverUncurry W =
      (W.app (Opposite.op ⦋n⦌) a).val := by
  rw [← sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp,
    sliceOverUncurry_yoneda]

/-- 同じ四角形の全パラメーターの評価は、内側時間の合成単体を外側時間で切断した図式。 -/
lemma coherentCompositionSquare_evaluate_cut
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (s t : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (coherentCompositionSquare X Y Z).app (Opposite.op ⦋n⦌)
      (s, (t, (ULift.up σ, ULift.up τ))) =
    (SimplicialNerve C).map
      (SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv s).toOrderHom)).op
      (coherentCompositionSimplex σ τ (stdSimplex.objEquiv t).toOrderHom) := by
  change (sliceOverUncurry (coherentCompositionPrism X Y Z)).app (Opposite.op ⦋n⦌)
    ((rightMappingSpacePrism _).app (Opposite.op ⦋n⦌)
      (s, (t, (ULift.up σ, ULift.up τ)))) = _
  rw [rightMappingSpacePrism_evaluate, sliceOverUncurry_simplex_coordinate]
  change (SimplicialNerve C).map _
    (SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (coherentCompositionSimplex σ τ (stdSimplex.objEquiv t).toOrderHom))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 同じ四角形の対角の各単体は、同じ時刻の合成切断図式。 -/
lemma coherentCompositionSquare_evaluate_diagonal
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (coherentCompositionSquare X Y Z).app (Opposite.op ⦋n⦌)
      (t, (t, (ULift.up σ, ULift.up τ))) =
      coherentCompositionDiagonalCutSimplex σ τ (stdSimplex.objEquiv t).toOrderHom :=
  coherentCompositionSquare_evaluate_cut σ τ t t

end SerrePositivity.InfinityCategories
