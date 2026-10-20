module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaPostcompositionCone
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralConePrimitive

/-! # 一般最後外ホーンの残差を Yoneda 加群 cone への Hom で表す

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
variable {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実最後閉射の Yoneda 像の加群 cone。 -/
abbrev dgGeneralLastHornYonedaCone : ModuleCategory A D :=
  dgYonedaClosedCone A D (dgGeneralLastHornFinalClosed σ)

omit [Small.{u} D] in
/-- 最後閉射から閉 cycle を戻しても、実後合成鎖写像は厳密に同じ。 -/
lemma dgGeneralLastHornPostcomposition_eq_closed :
    dgGeneralLastHornPostcomposition σ = dgCyclePostcomposition A D ((HornData.knownData σ).obj 0)
      (closedHomEquiv A D _ _ (dgGeneralLastHornFinalClosed σ)) :=
  congrArg (dgCyclePostcomposition A D ((HornData.knownData σ).obj 0))
    ((closedHomEquiv A D _ _).apply_symm_apply (dgGeneralLastHornFinalCycle σ)).symm

/-- 元の指定 Hom cone と、表現可能加群から最後辺の加群 cone への Hom の実鎖同型。 -/
def dgGeneralLastHornYonedaConeIso : dgGeneralLastHornResidualCone σ ≅
    moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ)) :=
  (eqToIso (congrArg (fun f : homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (dgLastHornPenultimate n)) ⟶
      homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj (Fin.last (n +
        2))) =>
        mappingCone f) (dgGeneralLastHornPostcomposition_eq_closed σ))) ≪≫
    dgYonedaPostcompositionConeIso A D ((HornData.knownData σ).obj 0)
      (dgGeneralLastHornFinalClosed σ)

/-- 指定された元の (R,K) を、最後辺の加群 cone への Hom へ厳密に移した残差。 -/
def dgGeneralLastHornYonedaResidual :
    (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).X (-(n : ℤ)) :=
  (dgGeneralLastHornYonedaConeIso σ).hom.f (-(n : ℤ)) (dgGeneralLastHornConeResidual σ)

/-- 移した実残差も次数 −n の閉元。 -/
lemma dgGeneralLastHornYonedaResidual_closed :
    (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
      (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).d (-(n : ℤ)) (-(n : ℤ) + 1)
        (dgGeneralLastHornYonedaResidual σ) = 0 := by
  have hc := ConcreteCategory.congr_hom ((dgGeneralLastHornYonedaConeIso σ).hom.comm (-(n :
    ℤ)) (-(n : ℤ) + 1))
    (dgGeneralLastHornConeResidual σ)
  simpa only [ModuleCat.comp_apply, dgGeneralLastHornConeResidual_closed, map_zero,
    dgGeneralLastHornYonedaResidual] using hc

/-- 実二未知解の存在を、同じ指定残差の加群 Hom 内の境界性へ帰着する。 -/
lemma dgGeneralLastHornSolution_nonempty_iff_yonedaResidual_boundary :
    Nonempty (DGGeneralLastHornSolution σ) ↔
      ∃ h : (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
          (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).X (-(n : ℤ) - 1),
        (moduleHom A D (representable A ((HornData.knownData σ).obj 0))
          (ForgetEnrichment.to (Complex A) (dgGeneralLastHornYonedaCone σ))).d (-(n : ℤ) - 1)
            (-(n : ℤ)) h =
            dgGeneralLastHornYonedaResidual σ :=
  (dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary σ).trans
    (dgComplexIso_exists_primitive_iff A (dgGeneralLastHornYonedaConeIso σ).hom (-(n : ℤ) -
      1) (-(n : ℤ))
      (dgGeneralLastHornConeResidual σ)).symm

end SerrePositivity.InfinityCategories
