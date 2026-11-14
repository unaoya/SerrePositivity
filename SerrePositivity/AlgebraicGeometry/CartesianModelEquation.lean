module

public import SerrePositivity.AlgebraicGeometry.FiniteCompositeStageEqualities
public import SerrePositivity.AlgebraicGeometry.CoefficientSubalgebraFactor

/-!
概要：元の比較の後で一致する模型間の二射を、実際の共通係数段で同時に一致させる。
方針：具体的な源模型・比較・二射を有限族として、既存の同時一致判定へ渡す。
規約：模型の存在を主定理の仮定に加えるものではなく、供給済みの式の入力の整理。
使われ方：G2 の六種の式を同じ有限段へそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v w

/-- 同じ係数基底上の実際の Cartesian 源模型と、その比較の後で一致する二射の入力。 -/
structure CartesianModelEquation {T S : Scheme.{u}} (g : T ⟶ S) where
  sourceModel : Scheme.{u}
  source : Scheme.{u}
  targetModel : Scheme.{u}
  sourceMap : sourceModel ⟶ S
  targetMap : targetModel ⟶ S
  comparison : source ⟶ sourceModel
  base : source ⟶ T
  cartesian : IsPullback comparison base sourceMap g
  left : sourceModel ⟶ targetModel
  right : sourceModel ⟶ targetModel
  leftOver : left ≫ targetMap = sourceMap
  rightOver : right ≫ targetMap = sourceMap
  atLimit : comparison ≫ left = comparison ≫ right
  sourceQC : QuasiCompact sourceMap
  sourceQS : QuasiSeparated sourceMap
  targetFP : LocallyOfFinitePresentation targetMap

/-- 有限個の元の比較の後での式を、実際の有限生成係数部分代数の同じ段での式へ降ろす。 -/
theorem CartesianModelEquation.exists_coefficient_stage
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (A : Subalgebra k R) (hA : A.FG) {ι : Type w} [Finite ι]
    (a : ι → CartesianModelEquation (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    ∃ (s : Finset R)
      (γ : (coefficientSpecDiagram k R).obj (.op s) ⟶ Spec (CommRingCat.of A)),
      (coefficientSpecCone k R).π.app (.op s) ≫ γ =
          Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧
      ∀ e, baseChangedModelArrow γ (a e).sourceMap (a e).targetMap (a e).left (a e).leftOver =
        baseChangedModelArrow γ (a e).sourceMap (a e).targetMap (a e).right (a e).rightOver := by
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
  obtain ⟨s, γ, hγ⟩ := exists_coefficient_spec_factor_of_fg k R A hA
  haveI (b : (Finset R)ᵒᵖ) : CompactSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (b : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI {b d : (Finset R)ᵒᵖ} (q : b ⟶ d) : IsAffineHom (D.map q) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  letI (e : ι) : QuasiCompact (a e).sourceMap := (a e).sourceQC
  letI (e : ι) : QuasiSeparated (a e).sourceMap := (a e).sourceQS
  letI (e : ι) : LocallyOfFinitePresentation (a e).targetMap := (a e).targetFP
  obtain ⟨j, hj⟩ := exists_finite_compositeStage_equalities_of_isLimit D c hc (.op s) γ _ hγ
    (fun e ↦ (a e).sourceModel) (fun e ↦ (a e).source) (fun e ↦ (a e).targetModel)
    (fun e ↦ (a e).sourceMap) (fun e ↦ (a e).targetMap)
    (fun e ↦ (a e).comparison) (fun e ↦ (a e).base) (fun e ↦ (a e).cartesian)
    (fun e ↦ (a e).left) (fun e ↦ (a e).right)
    (fun e ↦ (a e).leftOver) (fun e ↦ (a e).rightOver) (fun e ↦ (a e).atLimit)
  refine ⟨j.left.unop, D.map j.hom ≫ γ, ?_, hj⟩
  rw [← Category.assoc, c.w, hγ]

end SerrePositivity.AlgebraicGeometry
