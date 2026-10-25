module

public import SerrePositivity.BhattScholze.Delta.Distinguished
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionPDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Jacobson

/-! # 実導来p除算候補の具体的な単元係数

既存の実H⁰候補にG6を適用する。古典的完備化への置換は行わない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
attribute [local instance] derivedDeltaDivisionCommRing
local notation "U₀" => DeltaDivisionTorsionQuotient D (p : A) a
local notation "C₀" => DerivedDeltaDivisionCompletion D (p : A) a
local notation "j₀" => deltaDivisionTorsionMap D (p : A) a

/-- 除算変数の既存実導来完備化H⁰への標準像。 -/
def derivedPDivisionVariable (s : σ) : C₀ :=
  pdCompletionUnit U₀ p ((j₀) (p : A))
    (Ideal.Quotient.mk _ (deltaAdjoinDivisionVariable D (p : A) a s))

/-- 実候補内の標準除算変数はp*u_s=j(a_s)を満たす。 -/
theorem derivedPDivisionVariable_relation (s : σ) :
    (p : C₀) * derivedPDivisionVariable D a s =
      derivedDeltaDivisionMap D (p : A) a (a s) := by
  let q : DeltaAdjoinDivision D (p : A) a →+* U₀ := Ideal.Quotient.mk _
  let k := (pdCompletionUnit U₀ p ((j₀) (p : A))).comp q
  have h := congrArg k (deltaAdjoinDivision_relation D (p : A) a s)
  rw [map_mul] at h
  have hk : k (deltaAdjoinDivisionMap D (p : A) a (p : A)) = (p : C₀) := by
    simp only [map_natCast]
  rw [hk] at h
  exact h

/-- G6により、実導来p除算候補内のpはJacobson根基に属する。 -/
theorem derivedPDivision_p_mem_jacobson : (p : C₀) ∈ Ideal.jacobson (⊥ : Ideal C₀) :=
  mem_jacobson_bot_of_isModuleComplete C₀ (p : C₀)
    (derivedDeltaDivision_complete_p D (p : A) a)

/-- distinguished入力の標準除算変数像は実導来候補内でも単元。 -/
theorem derivedPDivisionVariable_isUnit (s : σ) (ha : D.IsDistinguished (a s)) :
    IsUnit (derivedPDivisionVariable D a s) := by
  have hp := derivedPDivision_p_mem_jacobson D a
  apply (DeltaStructure.isDistinguished_factor (derivedDeltaDivisionStructure D (p : A) a)
    (p : C₀) (derivedPDivisionVariable D a s) ?_ hp hp).2
  rw [derivedPDivisionVariable_relation]
  exact (derivedDeltaDivisionMap_isDeltaHom D (p : A) a).map_isDistinguished ha

/-- 実導来候補における、指定変数像そのもので与えられる単元係数。 -/
theorem exists_derivedPDivision_unit_factor (s : σ) (ha : D.IsDistinguished (a s)) :
    ∃ u : C₀ˣ, (u : C₀) = derivedPDivisionVariable D a s ∧
      derivedDeltaDivisionMap D (p : A) a (a s) = p * (u : C₀) := by
  obtain ⟨u, hu⟩ := derivedPDivisionVariable_isUnit D a s ha
  exact ⟨u, hu, by rw [hu]; exact (derivedPDivisionVariable_relation D a s).symm⟩

end SerrePositivity.BhattScholze
