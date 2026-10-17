module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseSequential
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # dg 加群の可算余極限と telescope cone の擬同型

次数ごとの 1-shift の単射性と cokernel の普遍性を用いる。遷移射の単射性は不要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : ℕ ⥤ ModuleCategory A D) (s : Cocone F)

def moduleSequentialShortComplex : ShortComplex (ModuleCategory A D) :=
  ShortComplex.mk (sequentialCoproductMap.{u} F) (sequentialCoproductDesc.{u} F s)
    (sequentialCoproductMap_desc.{u} F s)

lemma moduleSequentialShortComplex_evaluation_shortExact (hs : IsColimit s) (x : D) :
    ((moduleSequentialShortComplex A D F s).map (moduleEvaluation A D x)).ShortExact := by
  let E := moduleEvaluation A D x
  let S := (moduleSequentialShortComplex A D F s).map E
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    (isColimitMapCoconeCoforkEquiv' E (sequentialCoproductMap_desc.{u} F s)).toFun
      (isColimitOfPreserves E (sequentialCoproductCokernel.{u} F s hs))
  have hm : Mono S.f := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact sequentialCoproductMap_mono_of_moduleCat_functor A F
      (E ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)
  exact {
    exact := S.exact_of_g_is_cokernel hc
    mono_f := hm
    epi_g := epi_of_isColimit_cofork hc }

def moduleSequentialConeDesc : moduleCone A D (sequentialCoproductMap.{u} F) ⟶ s.pt :=
  moduleConeDesc A D _ _ (sequentialCoproductMap_desc.{u} F s)

set_option maxHeartbeats 800000 in
-- 評価された豊穣加群 cone と通常の mapping cone の型の定義展開に必要。
lemma moduleSequentialConeDesc_quasiIso (hs : IsColimit s) :
    moduleQuasiIso A D (moduleSequentialConeDesc A D F s) := by
  intro x
  dsimp only [moduleSequentialConeDesc]
  rw [moduleConeDesc_eval]
  have h := mappingCone.quasiIso_descShortComplex
    (moduleSequentialShortComplex_evaluation_shortExact A D F s hs x)
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded
