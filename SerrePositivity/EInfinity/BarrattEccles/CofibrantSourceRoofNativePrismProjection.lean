module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismProjection
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrism
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofEvaluationHomotopy

/-!
# 実 native prism の底は元の標準評価円柱

概要：実 qY slice への全 prism の射影を元の EvaluationHomotopy の全 h と同定する。
方針：一般の元の前面の式を実 comma 図式へそのまま代入する。
規約：任意可換環・元の評価円柱・全パラメータを保持する。
使われ方：native roof 全三角形の標準左脚。両端の同定は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaNativePrism_projection :
    cofibrantSourceRoofProductCommaNativePrism A X Y b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (cofibrantHammockVertex A Y)) =
    (β_ (Δ[1] : SSet.{u + 1}) (nerve (cofibrantSourceRoofProductComma A X Y b))).hom ≫
      (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b).h := by
  rw [cofibrantSourceRoofProductCommaEvaluationHomotopy_h A X Y b]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, Γ⟩
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (cofibrantSourceRoofProductCommaNativeSimplex A X Y b Γ
      (stdSimplex.objEquiv t).toOrderHom)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  have hf := RoofPrefix.simplex_front (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) Γ
    (stdSimplex.objEquiv t).toOrderHom
  refine hf.trans ?_
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory (cofibrantAlgebraRelativeCategory A))).app
    (Opposite.op ⦋n⦌) (RoofPrefix.frontDiagram (cofibrantAlgebraRelativeCategory A)
      (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation A X Y b) Γ
      (stdSimplex.objEquiv t).toOrderHom) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory (cofibrantAlgebraRelativeCategory A))).app
      (Opposite.op ⦋n⦌) (((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
        (cofibrantSourceRoofProductCommaEvaluation A X Y b)).h.app (Opposite.op ⦋n⦌)
          (Γ, t)) ⋙ kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveNatTransHomotopy_app]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
