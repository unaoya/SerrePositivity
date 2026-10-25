module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionEvaluationSource

/-! # 一般除数・任意元族の自由δ射が与える実代数構造 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意元族cへの実自由δ評価βによる係数環の源代数構造。 -/
@[instance_reducible]
def deltaDivisionSourceEvaluationAlgebra (D : DeltaStructure p A) (c : σ → A) :
    Algebra (RelativeFreeDeltaRing (R := A) σ) A :=
  (deltaDivisionSourceEval D c).toAlgebra

/-- 実自由δ射α:x_s↦d z_sによる終域の源代数構造。 -/
@[instance_reducible]
def deltaDivisionSourceTargetAlgebra (D : DeltaStructure p A) (d : A) :
    Algebra (RelativeFreeDeltaRing (R := A) σ) (RelativeFreeDeltaRing (R := A) σ) :=
  (deltaDivisionSourceMap (σ := σ) D d).toAlgebra

/-- 評価代数構造の実係数射は指定したβそのもの。 -/
theorem deltaDivisionSourceEvaluationAlgebra_algebraMap (D : DeltaStructure p A) (c : σ → A) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    algebraMap (RelativeFreeDeltaRing (R := A) σ) A = deltaDivisionSourceEval D c := rfl

/-- 終域代数構造の実係数射は指定したαそのもの。 -/
theorem deltaDivisionSourceTargetAlgebra_algebraMap (D : DeltaStructure p A) (d : A) :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    algebraMap (RelativeFreeDeltaRing (R := A) σ) (RelativeFreeDeltaRing (R := A) σ) =
      deltaDivisionSourceMap (σ := σ) D d := rfl

end SerrePositivity.BhattScholze
