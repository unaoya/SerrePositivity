module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismProjection
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet MonoidalCategory SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativePrism_projection :
    modelBifibrantSourceRoofProductCommaNativePrism X Y q b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (modelBifibrantHammockVertex Y)) =
    (β_ (Δ[1] : SSet.{max u v}) (nerve (modelBifibrantSourceRoofProductComma X Y q b))).hom ≫
      (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b).h := by
  rw [modelBifibrantSourceRoofProductCommaEvaluationHomotopy_h X Y q b]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, Γ⟩
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ
      (stdSimplex.objEquiv t).toOrderHom)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  have hf := RoofPrefix.simplex_front (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) Γ
    (stdSimplex.objEquiv t).toOrderHom
  refine hf.trans ?_
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))).app
    (Opposite.op ⦋n⦌) (RoofPrefix.frontDiagram (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
      (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
      (modelBifibrantSourceRoofProductCommaEvaluation X Y q b) Γ
      (stdSimplex.objEquiv t).toOrderHom) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))).app
      (Opposite.op ⦋n⦌) (((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
        (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)).h.app (Opposite.op ⦋n⦌)
          (Γ, t)) ⋙ kanHammockSourceFunctor (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveNatTransHomotopy_app]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
