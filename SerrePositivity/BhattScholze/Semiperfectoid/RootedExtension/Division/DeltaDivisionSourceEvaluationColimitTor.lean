module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionSourceEvaluationColimit
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits

/-! # G7交換入力に相対的な任意一元評価環へのTor移送

BSの具体的な有限グラフ商図式だけを扱う。
標準PreservesColimit入力を公開型に保持し、共通G7のTor消滅補題を再利用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (a : σ → A)
variable {T : Type u} [CommRing T]
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram D a

/-- 実有限グラフ商のTor消滅は、明示したG7交換入力の下で全評価環Aへ移る。 -/
theorem deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
    (φ : P₀ →+* T) (i : ℕ)
    (hfin : ∀ N : ℕ, Subsingleton (SerrePositivity.TorAlg φ (i + 1)
      (DeltaDivisionEvaluationSourceFiniteQuotient D a N)))
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    Subsingleton (SerrePositivity.TorAlg φ (i + 1) A) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  have := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F₀)) :=
    torAlg_colimit_isZero_of_stages φ F₀ (i + 1)
      (fun N => ModuleCat.isZero_iff_subsingleton.mpr (hfin N))
  let e : H.obj (ModuleCat.of P₀ A) ≅ H.obj (colimit F₀) :=
    H.mapIso (deltaDivisionEvaluationSourceFiniteColimitEvalIso D a).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

end SerrePositivity.BhattScholze
