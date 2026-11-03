module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：元の実加群 cone の逆 shift から元始域への指定閉射を構成する。
方針：元 connecting map を逆 shift し、同じ加法・零 shift 同型で始域を回収する。
規約：元の実 cone と shift の符号を保持。使われ方：LT 逆回転の実比較辺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {M N : ModuleCategory R E} (f : M ⟶ N)

/-- 概要：同じ実 cone の逆 shift から元始域への指定射。
方針：元 connecting map と同じ shift の指定比較だけを合成する。
規約：対象の選び直しなし。使われ方：逆回転の同じ実零次比較。 -/
def dgModuleLoopConeProjection :
    ForgetEnrichment.of (Complex R)
      (shiftModule (-1) (ForgetEnrichment.to (Complex R) (moduleCone R E f))) ⟶ M :=
  (moduleShiftFunctor R E (-1)).map (moduleConeConnecting R E f) ≫
    (moduleShiftAddIsoObj R E 1 (-1) (ForgetEnrichment.to (Complex R) M)).inv ≫
    (moduleShiftZeroIsoObj R E (ForgetEnrichment.to (Complex R) M)).hom

/-- 概要：元加群射の各評価は同じ connecting map の逆 shift と指定比較の合成。
方針：評価の関手則と既存の shift・connecting 比較式を使う。
規約：元の射を保持。使われ方：逆回転の全 Hom 自然性の評価計算。 -/
lemma dgModuleLoopConeProjection_eval (x : E) :
    (moduleEvaluation R E x).map (dgModuleLoopConeProjection R E f) =
      ((mappingCone.triangle ((moduleEvaluation R E x).map f)).mor₃)⟦(-1 : ℤ)⟧' ≫
        ((shiftFunctorAdd (Complex R) 1 (-1)).app
          ((moduleEvaluation R E x).obj M)).inv ≫
        ((shiftFunctorZero (Complex R) ℤ).app ((moduleEvaluation R E x).obj M)).hom := by
  unfold dgModuleLoopConeProjection
  apply ((moduleEvaluation R E x).map_comp _ _).trans
  apply congrArg₂ (fun a b => a ≫ b)
  · exact (moduleShiftFunctor_map_eval R E (-1) (moduleConeConnecting R E f) x).trans
      (congrArg (fun a => a⟦(-1 : ℤ)⟧') (moduleConeConnecting_eval R E f x))
  · exact ((moduleEvaluation R E x).map_comp _ _).trans
      (congrArg₂ (fun a b => a ≫ b)
        (moduleShiftAddIsoObj_inv_eval R E 1 (-1) (ForgetEnrichment.to (Complex R) M) x)
        (moduleShiftZeroIsoObj_hom_eval R E (ForgetEnrichment.to (Complex R) M) x))
end SerrePositivity.KST.SConstruction
