module

public import SerrePositivity.KST.DerivedBlowup.DiagramHomGauge
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory

/-!
概要：KST §3.1 の証明済み Hom 重み付けを実際の係数 dg 自己関手にする。
方針：包含上の Hom 同定で自己同型を移し、指定単位・積整合性で dg 関手則を示す。
規約：係数圏の対象と Hom 複体を保持する。
使われ方：整数捻りの大域 dg 加群への作用。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：証明済み重み付けを係数圏の各 Hom 複体の自己同型へ移す。
方針：包含があれば目標代数との標準同定を使い、なければ零複体の恒等にする。
規約：KST §3.1。使われ方：指定 dg 自己関手の Hom 写像。 -/
def diagramGaugeHomIso (i j : J) : diagramModuleHom F i j ≅ diagramModuleHom F i j :=
  if h : i ≤ j then
    eqToIso (diagramModuleHom_of_le F h) ≪≫ s.scale h ≪≫
      (eqToIso (diagramModuleHom_of_le F h)).symm
  else Iso.refl _

/-- 概要：包含上の重み付けは局所代数の指定自己同型そのものになる。
方針：Hom 同定の順逆の移送を消去する。
規約：KST §3.1。使われ方：単位・合成の保存の計算。 -/
theorem diagramGaugeHomIso_inclusion {i j : J} (h : i ≤ j) :
    diagramModuleHomInclusion F h ≫ (diagramGaugeHomIso F s i j).hom =
      (s.scale h).hom ≫ diagramModuleHomInclusion F h := by
  simp only [diagramGaugeHomIso, dite_eq_left h, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, diagramModuleHomInclusion]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option maxHeartbeats 2000000 in
-- 包含上の Hom 同定と二つの tensor 合成の型を照合するために必要。
/-- 概要：証明済み Hom 重み付けによる係数 dg 圏の指定自己関手。
方針：対角での恒等条件と係数遷移後の積の整合式から圏法則を導く。
規約：KST §3.1、元の係数圏と大域 dg 模型を保持する。
使われ方：構造加群を制限して整数捻りを作る。 -/
def diagramGaugeDGFunctor : DGFunctor R (DiagramModuleCoefficientObject F)
    (DiagramModuleCoefficientObject F) where
  obj x := x
  map x y := (diagramGaugeHomIso F s x.index y.index).hom
  map_id x := by
    change diagramModuleId F x.index ≫ (diagramGaugeHomIso F s x.index x.index).hom =
      diagramModuleId F x.index
    simp only [diagramModuleId]
    rw [Category.assoc, diagramGaugeHomIso_inclusion, s.scale_id]
    simp only [Iso.refl_hom, Category.id_comp]
  map_comp x y z := by
    change diagramModuleComp F x.index y.index z.index ≫
        (diagramGaugeHomIso F s x.index z.index).hom =
      ((diagramGaugeHomIso F s x.index y.index).hom ⊗ₘ
        (diagramGaugeHomIso F s y.index z.index).hom) ≫
        diagramModuleComp F x.index y.index z.index
    by_cases h : x.index ≤ y.index
    · by_cases g : y.index ≤ z.index
      · let : IsIso (diagramModuleHomInclusion F h) := by
          unfold diagramModuleHomInclusion
          infer_instance
        let : IsIso (diagramModuleHomInclusion F g) := by
          unfold diagramModuleHomInclusion
          infer_instance
        apply (cancel_epi (diagramModuleHomInclusion F h ⊗ₘ
          diagramModuleHomInclusion F g)).mp
        rw [← Category.assoc, diagramModuleComp_on_le, Category.assoc,
          Category.assoc, diagramGaugeHomIso_inclusion,
          tensorHom_comp_tensorHom_assoc, diagramGaugeHomIso_inclusion,
          diagramGaugeHomIso_inclusion, ← tensorHom_comp_tensorHom_assoc,
          diagramModuleComp_on_le]
        simpa only [diagramAlgebraMul, Category.assoc] using
          (congrArg (fun f => f ≫ diagramModuleHomInclusion F (h.trans g))
            (s.scale_comp h g)).symm
      · simp only [diagramModuleComp, dite_eq_left h, dite_eq_right g,
          Limits.zero_comp, Limits.comp_zero]
    · simp only [diagramModuleComp, dite_eq_right h, Limits.zero_comp, Limits.comp_zero]

/-- 概要：重み付け自己関手は全ての Hom 複体で同型を与える。
方針：指定 Hom 写像が構成済み複体自己同型の順射であることを使う。
規約：KST §3.1。使われ方：捻りの局所導来 Hom の保持。 -/
theorem diagramGaugeDGFunctor_map_isIso (x y : DiagramModuleCoefficientObject F) :
    IsIso ((diagramGaugeDGFunctor F s).map x y) := by
  change IsIso (diagramGaugeHomIso F s x.index y.index).hom
  infer_instance

end SerrePositivity.KST.DerivedBlowup
