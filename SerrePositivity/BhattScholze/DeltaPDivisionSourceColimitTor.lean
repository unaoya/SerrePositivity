module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceFiniteColimit

/-! # G7の交換入力に相対的な全源評価環へのTor移送

標準MathlibのPreservesColimitを明示的に受け取る。
この入力自体を証明したり、G7を受領したりしたという主張ではない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "F₀" => deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y

/-- G7の標準colimit交換入力があれば、全源評価環Aの正次数Torが零。
PreservesColimitの入力は未解消の共通基盤への要求として明示している。 -/
theorem deltaPDivisionSource_tor_subsingleton_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℕ)
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1) A) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  have := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1)
  have hz : IsZero (colimit (F₀ ⋙ H)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    have hN : IsZero ((F₀ ⋙ H).obj N) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (SerrePositivity.TorAlg α₀ (i + 1)
        (DeltaPDivisionSourceFiniteQuotient (σ := σ) D y N))
      exact deltaPDivisionSourceFinite_tor_subsingleton D y hpA hg v hv hy N i
    exact hN.eq_of_src _ _
  let e : H.obj (ModuleCat.of P₀ A) ≅ colimit (F₀ ⋙ H) :=
    H.mapIso (deltaDivisionSourceFiniteColimitEvalIso D y).symm ≪≫ preservesColimitIso H F₀
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

end SerrePositivity.BhattScholze
