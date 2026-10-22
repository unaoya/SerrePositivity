module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeComposition

/-! # 実加群 cone の単位の三成分表示
概要：左右の実単位と第三成分零が元の cone の単位を回収する。
方針：元の加群評価で同じ閉恒等 cochain と cone 恒等式へ戻す。
規約：実 end 内の等号を証明する。使われ方：cone Hom 写像の単位保存。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 元の実加群単位の評価は、同じ評価対象の恒等 cochain。 -/
lemma dgGluingModuleUnit_π (M : ModuleCategory R E) (x : E) :
    (moduleHomπ R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M) x).f 0
        (unitElement R (ForgetEnrichment.to (Complex R) M)).val =
      Cochain.ofHom (𝟙 ((moduleEvaluation R E x).obj M)) := by
  have h := (moduleEvaluation_cochain R E x (𝟙 M)).symm
  rw [ForgetEnrichment.homTo_id] at h
  exact h.trans (congrArg Cochain.ofHom ((moduleEvaluation R E x).map_id M))

/-- 左右の元の単位と第三成分零は、元の実加群 cone の単位に一致する。 -/
lemma dgGluingModuleConeElement_identity {M N : ModuleCategory R E} (f : M ⟶ N) :
    dgGluingModuleConeElement R E f f
      (unitElement R (ForgetEnrichment.to (Complex R) M)).val
      (unitElement R (ForgetEnrichment.to (Complex R) N)).val
      (0 : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) N)).X (-1)) (by omega) =
      (unitElement R (ForgetEnrichment.to (Complex R) (moduleCone R E f))).val := by
  apply moduleHomElement_ext R E
  intro x
  simp only [dgGluingModuleConeElement_π, dgGluingModuleUnit_π, map_zero]
  exact dgGluingConeCochain_identity _

end SerrePositivity.KST.SConstruction
