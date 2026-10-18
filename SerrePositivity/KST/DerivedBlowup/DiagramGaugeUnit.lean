module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeFunctor
public import SerrePositivity.KST.DerivedBlowup.DiagramStructureUnitTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnitActionGeneral

/-!
概要：KST §3.1 の Hom gauge で重み付けした包含単位を追跡する。
方針：Hom 同定との整合性を使い、補助始点つき係数圏への像まで計算する。
規約：加群作用の前に指定閉零係数射自体の等式を保持する。
使われ方：O(m) の局所生成元と canonical な指定遷移の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：gauge が包含単位に作用した像は局所単位への重み付け。
方針：指定包含の Hom 同定との整合式を単位射で前合成する。
規約：KST §3.1。使われ方：捻り加群の指定遷移の閉零係数射。 -/
theorem diagramGaugeDGFunctor_unit {i j : J} (h : i ≤ j) :
    diagramModuleTransitionUnit F h ≫ (diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩ =
      MonObj.one (X := (F.obj j).X) ≫ (s.scale h).hom ≫ diagramModuleHomInclusion F h := by
  change (MonObj.one (X := (F.obj j).X) ≫ diagramModuleHomInclusion F h) ≫
    (diagramGaugeHomIso F s i j).hom = _
  rw [Category.assoc, diagramGaugeHomIso_inclusion]

/-- 概要：補助係数圏への包含は全ての包含 Hom の指定同定と可換。
方針：元の Hom 同定と補助係数圏への等式移送を合成する。
規約：KST §3.1。使われ方：重み付けされた包含単位を補助 representable へ送る。 -/
theorem diagramAlgebraBottomInclusion_homInclusion {i j : J} (h : i ≤ j) :
    diagramModuleHomInclusion F h ≫ (diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩ =
      diagramModuleHomInclusion (diagramAlgebraWithBottom F) (WithBot.coe_le_coe.mpr h) := by
  change diagramModuleHomInclusion F h ≫ eqToHom (diagramAlgebraWithBottom_hom F i j) = _
  simp only [diagramModuleHomInclusion, eqToHom_trans]

/-- 概要：重み付け包含単位の補助係数圏への像の指定式。
方針：gauge の単位公式と補助包含の Hom 同定の整合性を合成する。
規約：KST §3.1。使われ方：捻り生成元の representable 作用の計算。 -/
theorem diagramGaugeDGFunctor_bottom_unit {i j : J} (h : i ≤ j) :
    diagramModuleTransitionUnit F h ≫ (diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩ ≫
        (diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩ =
      MonObj.one (X := (F.obj j).X) ≫ (s.scale h).hom ≫
        diagramModuleHomInclusion (diagramAlgebraWithBottom F) (WithBot.coe_le_coe.mpr h) := by
  rw [← Category.assoc, diagramGaugeDGFunctor_unit, Category.assoc,
    Category.assoc, diagramAlgebraBottomInclusion_homInclusion]

/-- 概要：重み付け包含単位の補助係数圏への像を閉零 cycle 上で計算する。
方針：指定閉零射の等式を単位複体の生成元で評価する。
規約：KST §3.1。使われ方：捻り加群の局所生成元の遷移公式。 -/
theorem diagramGaugeDGFunctor_bottom_unit_cycle {i j : J} (h : i ≤ j) :
    ((diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩).f 0
      (((diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩).f 0
        (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val) =
      (diagramModuleHomInclusion (diagramAlgebraWithBottom F)
        (WithBot.coe_le_coe.mpr h)).f 0
        ((s.scale h).hom.f 0 (cycleFromUnit (F.obj j).X MonObj.one).val) := by
  have he := congrArg (fun f : 𝟙_ (Complex R) ⟶
      diagramModuleHom (diagramAlgebraWithBottom F) (i : WithBot J) (j : WithBot J) =>
      (cycleFromUnit _ f).val) (diagramGaugeDGFunctor_bottom_unit F s h)
  simp only [cycleFromUnit_postcomp] at he
  exact he

end SerrePositivity.KST.DerivedBlowup
