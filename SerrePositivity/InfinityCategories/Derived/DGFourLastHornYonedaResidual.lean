module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaPostcompositionCone
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornConePrimitive

/-! # 実四次最後外ホーンの残差を Yoneda 加群 cone への Hom で表す

概要：元の実残差を実鎖同型で移し、その閉性と原始元による二未知解の回収を保つ。
方針：最後閉射の cycle を厳密に戻し、後合成 cone の Yoneda 比較を適用する。
規約：移した残差は指定した元の (R,K) の像。使われ方：分母 cone の有限 cell 消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex CochainComplex HomComplex SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実最後閉射の Yoneda 像の加群 cone。 -/
abbrev dgFourLastHornYonedaCone : ModuleCategory A D :=
  dgYonedaClosedCone A D (dgFourLastHornFinalClosed σ)

omit [Small.{u} D] in
/-- 最後閉射から閉 cycle を戻しても、実後合成鎖写像は厳密に同じ。 -/
lemma dgFourLastHornPostcomposition_eq_closed :
    dgFourLastHornPostcomposition σ = dgCyclePostcomposition A D ((HornData.knownData σ).obj 0)
      (closedHomEquiv A D _ _ (dgFourLastHornFinalClosed σ)) :=
  congrArg (dgCyclePostcomposition A D ((HornData.knownData σ).obj 0))
    ((closedHomEquiv A D _ _).apply_symm_apply (dgFourLastHornFinalCycle σ)).symm

/-- 元の指定 Hom cone と、表現可能加群から最後辺の加群 cone への Hom の実鎖同型。 -/
def dgFourLastHornYonedaConeIso : dgFourLastHornResidualCone σ ≅
    moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ)) :=
  (eqToIso (congrArg (fun f : homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 3) ⟶
      homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4) =>
        mappingCone f) (dgFourLastHornPostcomposition_eq_closed σ))) ≪≫
    dgYonedaPostcompositionConeIso A D ((HornData.knownData σ).obj 0) (dgFourLastHornFinalClosed σ)

/-- 指定された元の (R,K) を、最後辺の加群 cone への Hom へ厳密に移した残差。 -/
def dgFourLastHornYonedaResidual :
    (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).X (-2) :=
  (dgFourLastHornYonedaConeIso σ).hom.f (-2) (dgFourLastHornConeResidual σ)

/-- 移した実残差も次数 −2 の閉元。 -/
lemma dgFourLastHornYonedaResidual_closed :
    (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).d (-2) (-1)
        (dgFourLastHornYonedaResidual σ) = 0 := by
  have hc := ConcreteCategory.congr_hom ((dgFourLastHornYonedaConeIso σ).hom.comm (-2) (-1))
    (dgFourLastHornConeResidual σ)
  simpa only [ModuleCat.comp_apply, dgFourLastHornConeResidual_closed, map_zero,
    dgFourLastHornYonedaResidual] using hc

/-- 実二未知解の存在を、同じ指定残差の加群 Hom 内の境界性へ帰着する。 -/
lemma dgFourLastHornSolution_nonempty_iff_yonedaResidual_boundary :
    Nonempty (DGFourLastHornSolution σ) ↔
      ∃ h : (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
          (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).X (-3),
        (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
          (ForgetEnrichment.to (Complex A) (dgFourLastHornYonedaCone σ))).d (-3) (-2) h =
            dgFourLastHornYonedaResidual σ :=
  (dgFourLastHornSolution_nonempty_iff_coneResidual_boundary σ).trans
    (dgComplexIso_exists_primitive_iff A (dgFourLastHornYonedaConeIso σ).hom (-3) (-2)
      (dgFourLastHornConeResidual σ)).symm

end SerrePositivity.InfinityCategories
