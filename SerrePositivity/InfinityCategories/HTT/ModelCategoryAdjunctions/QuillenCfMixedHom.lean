module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageProjection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：cf 対応圏の実際の混合射を元の右像への通常の射として回収する。
方針：豊穣単位との Hom 全単射を使い、両側の合成を元の Hom の式で照合。
規約：対象・合成を選び直さない。使われ方：cf 置換比較を実際の混合辺へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] (R : EnrichedFunctor SSet.{u} D C)
variable [ModelCategory C] [ModelCategory D]
open _root_.SerrePositivity.KST.SConstruction _root_.SerrePositivity.HomotopyFunctionComplex

/-- cf 対応圏の混合射と、元の右像への通常の射との全単射。 -/
def quillenCfMixedHomEquiv (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y) ≃ (X.obj ⟶ R.obj Y.obj) where
  toFun f := (eHomEquiv SSet (C := C)).symm (ForgetEnrichment.homTo SSet f.hom)
  invFun f := ⟨ForgetEnrichment.homOf SSet (eHomEquiv SSet (C := C) f)⟩
  left_inv f := by
    apply InducedCategory.hom_ext
    simp only [Equiv.apply_symm_apply]
    exact ForgetEnrichment.homOf_homTo SSet f.hom
  right_inv f := by
    exact (congrArg (eHomEquiv SSet (C := C)).symm
      (ForgetEnrichment.homTo_homOf SSet (eHomEquiv SSet (C := C) f))).trans
        ((eHomEquiv SSet (C := C)).symm_apply_apply f)

/-- 元の混合射の豊穣単位からの像は、同じ元の通常射の像に一致。 -/
lemma quillenCfMixedHomEquiv_eHom (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) (f : X.obj ⟶ R.obj Y.obj) :
    eHomEquiv SSet ((quillenCfMixedHomEquiv R X Y).symm f) =
      eHomEquiv SSet (C := C) f := by
  change ForgetEnrichment.homTo SSet (ForgetEnrichment.homOf SSet _) = _
  exact ForgetEnrichment.homTo_homOf SSet _

/-- 下段から混合射への後合成は、元の C での後合成そのもの。 -/
lemma quillenCfMixedHomWhiskerLeft (X W : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) (f : W.obj ⟶ R.obj Y.obj) :
    eHomWhiskerLeft SSet ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X)
        ((quillenCfMixedHomEquiv R W Y).symm f) =
      eHomWhiskerLeft SSet X.obj f := by
  unfold eHomWhiskerLeft
  rw [quillenCfMixedHomEquiv_eHom]
  rfl

/-- 混合射から上段への前合成は、元の右関手の Hom 作用を使う合成。 -/
lemma quillenCfMixedHomWhiskerRight (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (Y Z : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) (f : X.obj ⟶ R.obj Y.obj) :
    eHomWhiskerRight SSet ((quillenCfMixedHomEquiv R X Y).symm f)
        ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Z) =
      (λ_ (Y.obj ⟶[SSet] Z.obj)).inv ≫
        eHomEquiv SSet f ▷ _ ≫ (𝟙 _ ⊗ₘ R.map Y.obj Z.obj) ≫
          eComp SSet X.obj (R.obj Y.obj) (R.obj Z.obj) := by
  unfold eHomWhiskerRight
  rw [quillenCfMixedHomEquiv_eHom]
  rfl

/-- 任意の混合辺は、区間射影で標準の零から一への辺に写る。 -/
lemma quillenCfMixedEdge_projection (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)
    (e : (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))) :
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R).app (Opposite.op ⦋1⦌) e.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{max u v}).edge := by
  let e' := e.map (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
  have h0 := e'.src_eq.trans
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection_vertex R ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X))
  have h1 := e'.tgt_eq.trans
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection_vertex R ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj Y))
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  · have h := congrArg stdSimplex.obj₀Equiv h0
    exact h
  · have h := congrArg stdSimplex.obj₀Equiv h1
    exact h

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
