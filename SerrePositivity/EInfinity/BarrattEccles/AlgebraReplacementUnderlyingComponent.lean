module
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantForgetSourceComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorIsoEvaluationArrow
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponentArrow
/-!
概要：元の全代数の忘却比較の成分を、同じ置換 augmentation の導来像へ回収する。
方針：元の全源同型を評価し、等式輸送を全 Arrow で保持して比較する。
規約：元の代数・置換・通常忘却を保持する。
使われ方：標準単位と元の cofibrant 局所化源単位の端点整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：元の置換忘却同型の評価は同じ augmentation 成分の導来像。
方針：元の等式輸送を除去し、同じ通常自然変換の成分円柱を使う。
規約：元の同型の順射を保持。使われ方：実 U の源比較の右脚。 -/
lemma algebraReplacementUnderlyingDerivedIso_component_arrow (B : (operad A).Algebra) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (algebraReplacementUnderlyingDerivedIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (framedLimitProbeComparison A B).hom).map
          (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) := by
  let a := Functor.whiskerRight (framedLimitProbeComparisonNatTrans A)
    (Operad.Algebra.forget (operad A))
  have ha (Z : (operad A).Algebra) : QuasiIso (a.app Z) :=
    framedLimitProbeComparison_quasiIso A Z
  have he : algebraCAlgReplacementNerve A ≫ cofibrantAlgebraUnderlyingDerivedSource A =
      nerveMap (framedLimitProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        ComplexLimits.complexOrdinaryDerivedSource A := by
    rw [cofibrantAlgebraUnderlyingDerivedSource, ← Category.assoc,
      algebraCAlgReplacementNerve_forget]
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (nerveMap (framedLimitProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        ComplexLimits.complexOrdinaryDerivedSource A) (algebraUnderlyingDerivedSource A) :=
    ComplexLimits.complexOrdinaryDerivedNatTransIso A a ha
  have hd : algebraReplacementUnderlyingDerivedIso A =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) he) ≪≫ e := rfl
  rw [hd, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate_eqToIso_hom he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)]
  refine (Arrow.arrow_mk_eqToHom_comp _ _).trans ?_
  exact ComplexLimits.complexOrdinaryDerivedNatTransIso_component_arrow A a ha B

/-- 概要：通常複体頂点への比較は同じ全源同型の成分と全 Arrow として一致する。
方針：元の頂点等式の後合成輸送を Arrow の同じ射へ戻す。
規約：元の比較を保持。使われ方：全代数源比較の左脚の照合。 -/
lemma cofibrantForgetOrdinaryVertexIso_hom_arrow (B : CofibrantAlgebra A) :
    Arrow.mk (cofibrantForgetOrdinaryVertexIso A B).hom =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)) ≫
        eqToHom (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A B))) = _
  exact Arrow.arrow_mk_comp_eqToHom _ _

/-- 概要：元の全代数源の忘却比較は同じ置換頂点比較と augmentation の全合成。
方針：同じ全源同型の前合成評価と元の置換忘却成分を合成する。
規約：元の置換と実 U を保持。使われ方：自由 probe の標準端点の照合。 -/
lemma algebraCAlgSource_underlyingDerivedIso_component_arrow (B : (operad A).Algebra) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (algebraCAlgSource_underlyingDerivedIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) =
    Arrow.mk ((cofibrantForgetOrdinaryVertexIso A ((cofibrantAlgebraReplacement A).obj B)).hom ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (framedLimitProbeComparison A B).hom).map
          (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate_precomp_arrow (cAlgForgetDerived_sourceIso A)
    (algebraCAlgReplacementNerve A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)
  have hv := congrArg (fun v => (Arrow.mk
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom v) :
      Arrow (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)))) (algebraCAlgReplacementNerve_vertex A B)
  have hs' := (hs.trans hv).trans (cofibrantForgetOrdinaryVertexIso_hom_arrow A
    ((cofibrantAlgebraReplacement A).obj B)).symm
  rw [algebraCAlgSource_underlyingDerivedIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp]
  exact RoofPrefix.comp_arrow_eq _ _ _ _ hs'
    (algebraReplacementUnderlyingDerivedIso_component_arrow A B)

end SerrePositivity.EInfinity.BarrattEccles
