module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRestrictionMateComponents
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeUnit

/-!
概要：KST §3.1 の一般図式加群の捻り遷移と制限側 mate の比較。
方針：包含単位の gauge 像を計算し、次数零の二つの係数作用の結合則を使う。
規約：underlying 複体上の式は指定加群比較を評価して用いる。
使われ方：一般の canonical な cartesian 比較と graph の重み付けの可換式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：包含単位の cycle の gauge 像は局所重み単位の Hom 同定。
方針：指定閉零係数射の像を単位複体の生成元で評価する。
規約：KST §3.1。使われ方：一般加群の捻り遷移の斉次作用。 -/
theorem diagramGaugeDGFunctor_unit_cycle {i j : J} (h : i ≤ j) :
    ((diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩).f 0
        (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val =
      (diagramModuleHomInclusion F h).f 0
        (((s.scale h).hom.f 0) (unitElement R (.point : AlgebraVertex (F.obj j))).val) := by
  have he := congrArg (fun f : 𝟙_ (Complex R) ⟶ diagramModuleHom F i j =>
    (cycleFromUnit _ f).val) (diagramGaugeDGFunctor_unit F s h)
  simp only [cycleFromUnit_postcomp] at he
  exact he

variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：全図式加群圏上の指定 gauge 制限作用。
方針：構成済み係数 dg 自己関手に沿って制限する。
規約：KST §3.1。使われ方：整数捻り作用の一般形。 -/
abbrev diagramGaugeModuleAction :=
  moduleRestriction R (DiagramModuleCoefficientObject F)ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramGaugeDGFunctor F s).op.op

set_option maxHeartbeats 2000000 in
-- 二重 opposite の作用と局所制限の評価の型を照合するために必要。
/-- 概要：捻り加群の underlying 包含射は元の包含射と局所 mate の合成。
方針：二つの包含単位の作用を加群の結合則でまとめ、重み単位の像を同定する。
規約：KST §3.1。使われ方：指定局所比較の可換式を評価で証明する。 -/
theorem diagramGaugeModuleUnderlying_map {i j : J} (h : i ≤ j) (M : AllDiagramModules F) :
    (diagramModuleUnderlyingDiagram F
        (ForgetEnrichment.to (Complex R) ((diagramGaugeModuleAction F s).obj M))).map (homOfLE h) =
      (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) ≫
        (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
          ((diagramGaugeModuleRestrictionIso F s h).hom.app
            ((diagramAlgebraModuleEvaluation F j).obj M)) := by
  apply chain_ext_apply
  intro q v
  rw [chain_comp_apply]
  let N := ForgetEnrichment.to (Complex R) M
  let T := ForgetEnrichment.to (Complex R) ((diagramGaugeModuleAction F s).obj M)
  change (N.obj (op (op (⟨i⟩ : DiagramModuleCoefficientObject F)))).X q at v
  let t := (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val
  let c := ((s.scale h).hom.f 0) (unitElement R (.point : AlgebraVertex (F.obj j))).val
  let act : (N.obj (op (op (⟨j⟩ : DiagramModuleCoefficientObject F)))).X q →
      (N.obj (op (op (⟨j⟩ : DiagramModuleCoefficientObject F)))).X q := fun w =>
    moduleAction R N (x := op (op (⟨j⟩ : DiagramModuleCoefficientObject F)))
      (y := op (op ⟨j⟩)) ((diagramModuleHomInclusion F (le_refl j)).f 0 c) w (add_zero q)
  have hl := moduleClosedUnitAction_apply R T
    (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩))
    (diagramModuleTransitionUnit F h) q v
  have hr := moduleClosedUnitAction_apply R N
    (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩))
    (diagramModuleTransitionUnit F h) q
    (show (N.obj (op (op ⟨i⟩))).X q from v)
  have hb := diagramGaugeModuleRestrictionIso_apply F s h
    ((diagramAlgebraModuleEvaluation F j).obj M) q
    (show ((ForgetEnrichment.to (Complex R)
      ((diagramAlgebraModuleEvaluation F j).obj M)).obj (op (op .point))).X q from
      ((diagramModuleUnderlyingDiagram F N).map (homOfLE h)).f q v)
  change (((moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      ((diagramGaugeModuleRestrictionIso F s h).hom.app
        ((diagramAlgebraModuleEvaluation F j).obj M))).f q)
      (((diagramModuleUnderlyingDiagram F N).map (homOfLE h)).f q v) =
    act (((diagramModuleUnderlyingDiagram F N).map (homOfLE h)).f q v) at hb
  have he := moduleAction_forward R N
    (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩))
    (z := op (op ⟨j⟩)) t ((diagramModuleHomInclusion F (le_refl j)).f 0 c) v
    rfl (add_zero q) (add_zero q)
  rw [opposite_forward, opposite_forward] at he
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at he
  have ha := (congrArg (fun x => moduleAction R N
    (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩)) x v (add_zero q))
    (diagramModuleTransitionUnit_forward F h 0 c)).symm.trans he
  calc
    _ = moduleAction R N
        (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩))
        (((diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩).f 0 t)
        v (add_zero q) := hl
    _ = act (moduleAction R N
        (x := op (op (⟨i⟩ : DiagramModuleCoefficientObject F))) (y := op (op ⟨j⟩))
        t v (add_zero q)) := by
      rw [diagramGaugeDGFunctor_unit_cycle]
      exact ha
    _ = act (((diagramModuleUnderlyingDiagram F N).map (homOfLE h)).f q v) :=
      congrArg act hr.symm
    _ = _ := hb.symm

end SerrePositivity.KST.DerivedBlowup
