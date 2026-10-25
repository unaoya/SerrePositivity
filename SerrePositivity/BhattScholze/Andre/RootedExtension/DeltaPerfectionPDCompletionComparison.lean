module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaPerfectionPDCompletionUniversal
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDCompletion

/-! # δ完全化の直接PD完備化と既存p先行候補の標準環同型 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
variable (E : DeltaStructure p B) (b : B)
local notation "C" => DeltaPerfection E
local notation "P" => PCompletedDeltaPerfection E
local notation "x" => deltaPerfectionOf E 0 b
local notation "y" => pCompletedDeltaPerfectionMap E b
local notation "H₀" => PDCompletionH0 C p x
local notation "H₁" => PDCompletionH0 P p y
local notation "D₀" => deltaPDCompletionStructure (deltaPerfectionStructure E) x
local notation "D₁" => deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure E) y
local notation "r₀" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf E 0)
local notation "r₁" => RingHom.comp (pdCompletionUnit P p y) (pCompletedDeltaPerfectionMap E)

/-- 直接PD完備化から、既存のp先行PD完備化への標準δ射。 -/
def deltaPerfectionPDCompletionComparison :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ →+* H₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
    r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose

/-- 標準比較はδ射であり、元Bからの標準射を保つ。 -/
theorem deltaPerfectionPDCompletionComparison_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPerfectionPDCompletionComparison E b) ∧
      (deltaPerfectionPDCompletionComparison E b).comp r₀ = r₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
    r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose_spec.1

/-- 既存のp先行候補から直接PD完備化へ戻る標準δ射。 -/
def deltaPerfectionPDCompletionInverse :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₁ →+* H₀ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_pCompletedDeltaPerfectionPDCompletionHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose

/-- 逆方向の標準射もδ射であり、同じ元Bの標準射を保つ。 -/
theorem deltaPerfectionPDCompletionInverse_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₁).IsDeltaHom D₀ (deltaPerfectionPDCompletionInverse E b) ∧
      (deltaPerfectionPDCompletionInverse E b).comp r₁ = r₀ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_pCompletedDeltaPerfectionPDCompletionHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose_spec.1

/-- 直接PD完備化と既存p先行候補は、具体的な両標準δ射により環同型。 -/
def deltaPerfectionPDCompletionEquiv :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ ≃+* H₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  let f := deltaPerfectionPDCompletionComparison E b
  let g := deltaPerfectionPDCompletionInverse E b
  have hf := deltaPerfectionPDCompletionComparison_spec E b
  have hg := deltaPerfectionPDCompletionInverse_spec E b
  have hgf : g.comp f = RingHom.id H₀ := by
    apply deltaPerfectionPDCompletionHom_ext E b D₀
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
      r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
      (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)
      (g.comp f) (RingHom.id H₀) (hg.1.comp hf.1) (D₀).isDeltaHom_id ?_ (RingHom.id_comp r₀)
    rw [RingHom.comp_assoc, hf.2, hg.2]
  have hfg : f.comp g = RingHom.id H₁ := by
    apply pCompletedDeltaPerfectionPDCompletionHom_ext E b D₁
      (deltaPDCompletionStructure_isPerfect _ (pCompletedDeltaPerfection_isPerfect E) y)
      r₁ ((pdCompletionUnit_isDeltaHom _ _).comp (pCompletedDeltaPerfectionMap_isDeltaHom E))
      (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)
      (f.comp g) (RingHom.id H₁) (hf.1.comp hg.1) (D₁).isDeltaHom_id ?_ (RingHom.id_comp r₁)
    rw [RingHom.comp_assoc, hg.2, hf.2]
  exact RingEquiv.ofRingHom f g hfg hgf

/-- この環同型の両方向はδ射であり、元の標準raw射を保つ。 -/
theorem deltaPerfectionPDCompletionEquiv_spec :
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPerfectionPDCompletionEquiv E b).toRingHom ∧
      (D₁).IsDeltaHom D₀ (deltaPerfectionPDCompletionEquiv E b).symm.toRingHom ∧
      (deltaPerfectionPDCompletionEquiv E b).toRingHom.comp r₀ = r₁ := by
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact ⟨(deltaPerfectionPDCompletionComparison_spec E b).1,
    (deltaPerfectionPDCompletionInverse_spec E b).1,
    (deltaPerfectionPDCompletionComparison_spec E b).2⟩

end SerrePositivity.BhattScholze
