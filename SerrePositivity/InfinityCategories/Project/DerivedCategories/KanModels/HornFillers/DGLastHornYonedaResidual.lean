module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.DGYonedaPostcompositionCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornConePrimitive

/-! # 実最後外ホーンの残差を Yoneda 加群 cone への Hom で表す

概要：元の実残差を実鎖同型で移し、その閉性と原始元による二未知解の回収を保つ。
方針：最後閉射の cycle を厳密に戻し、後合成 cone の Yoneda 比較を適用する。
規約：移した残差は指定した元の (R,K) の像。使われ方：分母 cone の有限 cell 消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実最後閉射の Yoneda 像の加群 cone。 -/
abbrev dgLastHornYonedaCone : ModuleCategory A D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)

omit [Small.{u} D] in
/-- 最後閉射から閉 cycle を戻しても、実後合成鎖写像は厳密に同じ。 -/
lemma dgLastHornPostcomposition_eq_closed :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPostcomposition σ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)) :=
  congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
    ((closedHomEquiv A D _ _).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalCycle σ)).symm

/-- 元の指定 Hom cone と、表現可能加群から最後辺の加群 cone への Hom の実鎖同型。 -/
def dgLastHornYonedaConeIso : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornResidualCone σ ≅
    moduleHom A D (representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgLastHornYonedaCone σ)) :=
  (eqToIso (congrArg (fun f : homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) ⟶
      homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) =>
        mappingCone f) (dgLastHornPostcomposition_eq_closed σ))) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed σ)

/-- 指定された元の (R,K) を、最後辺の加群 cone への Hom へ厳密に移した残差。 -/
def dgLastHornYonedaResidual :
    (moduleHom A D (representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgLastHornYonedaCone σ))).X (-1) :=
  (dgLastHornYonedaConeIso σ).hom.f (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual σ)

/-- 移した実残差も次数 −1 の閉元。 -/
lemma dgLastHornYonedaResidual_closed :
    (moduleHom A D (representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgLastHornYonedaCone σ))).d (-1) 0
        (dgLastHornYonedaResidual σ) = 0 := by
  have hc := ConcreteCategory.congr_hom ((dgLastHornYonedaConeIso σ).hom.comm (-1) 0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual σ)
  simpa only [ModuleCat.comp_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual_closed, map_zero,
    dgLastHornYonedaResidual] using hc

/-- 実二未知解の存在を、同じ指定残差の加群 Hom 内の境界性へ帰着する。 -/
lemma dgLastHornSolution_nonempty_iff_yonedaResidual_boundary :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornSolution σ) ↔
      ∃ h : (moduleHom A D (representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgLastHornYonedaCone σ))).X (-2),
        (moduleHom A D (representable A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgLastHornYonedaCone σ))).d (-2) (-1) h =
            dgLastHornYonedaResidual σ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSolution_nonempty_iff_coneResidual_boundary σ).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexIso_exists_primitive_iff A (dgLastHornYonedaConeIso σ).hom (-2) (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornConeResidual σ)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
