module

public import SerrePositivity.BhattScholze.DeltaPDCompletionPerfectionUniversal
public import SerrePositivity.BhattScholze.PerfectDeltaPDCompletion

/-! # PD完備化をδ完全化の前へ挟む手順との標準環同型 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
variable (E : DeltaStructure p B) (b : B)
local notation "C" => DeltaPerfection E
local notation "S" => PDCompletionH0 B p b
local notation "G" => deltaPDCompletionStructure E b
local notation "v" => pdCompletionUnit B p b
local notation "P" => DeltaPerfection G
local notation "x" => deltaPerfectionOf E 0 b
local notation "y" => deltaPerfectionOf G 0 (v b)
local notation "H₀" => PDCompletionH0 C p x
local notation "H₁" => PDCompletionH0 P p y
local notation "D₀" => deltaPDCompletionStructure (deltaPerfectionStructure E) x
local notation "D₁" => deltaPDCompletionStructure (deltaPerfectionStructure G) y
local notation "r₀" => RingHom.comp (pdCompletionUnit C p x) (deltaPerfectionOf E 0)
local notation "r₁" => RingHom.comp
  (RingHom.comp (pdCompletionUnit P p y) (deltaPerfectionOf G 0)) v

/-- 直接PD完備化から、PD先行δ完全化後のPD完備化への標準δ射。 -/
def deltaPDCompletionPerfectionComparison :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ →+* H₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
    r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
      (pdCompletionUnit_isDeltaHom E b))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose

/-- 標準比較はδ射であり、元Bからの標準射を保つ。 -/
theorem deltaPDCompletionPerfectionComparison_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPDCompletionPerfectionComparison E b) ∧
      (deltaPDCompletionPerfectionComparison E b).comp r₀ = r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPerfectionPDCompletionHom E b D₁
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
    r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
      (pdCompletionUnit_isDeltaHom E b))
    (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)).choose_spec.1

/-- PD先行δ完全化後の候補から直接PD完備化へ戻る標準δ射。 -/
def deltaPDCompletionPerfectionInverse :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₁ →+* H₀ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPDCompletionPerfectionPDHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose

/-- 逆方向の標準射もδ射であり、同じ元Bの標準射を保つ。 -/
theorem deltaPDCompletionPerfectionInverse_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₁).IsDeltaHom D₀ (deltaPDCompletionPerfectionInverse E b) ∧
      (deltaPDCompletionPerfectionInverse E b).comp r₁ = r₀ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact (existsUnique_deltaPDCompletionPerfectionPDHom E b D₀
    (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
    r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
    (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)).choose_spec.1

/-- 直接PD完備化とPD先行δ完全化後の候補は、具体的な両標準δ射により環同型。 -/
def deltaPDCompletionPerfectionEquiv :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    H₀ ≃+* H₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  let f := deltaPDCompletionPerfectionComparison E b
  let g := deltaPDCompletionPerfectionInverse E b
  have hf := deltaPDCompletionPerfectionComparison_spec E b
  have hg := deltaPDCompletionPerfectionInverse_spec E b
  have hgf : g.comp f = RingHom.id H₀ := by
    obtain ⟨_, _, hu₀⟩ := existsUnique_deltaPerfectionPDCompletionHom E b D₀
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect E) x)
      r₀ ((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom E 0))
      (pdCompletionH0_self_complete_p C p x) (pdCompletionH0_self_complete_d C p x)
    apply (hu₀ (g.comp f) ⟨hg.1.comp hf.1, ?_⟩).trans
      (hu₀ (RingHom.id H₀) ⟨(D₀).isDeltaHom_id, RingHom.id_comp r₀⟩).symm
    rw [RingHom.comp_assoc, hf.2, hg.2]
  have hfg : f.comp g = RingHom.id H₁ := by
    obtain ⟨_, _, hu₁⟩ := existsUnique_deltaPDCompletionPerfectionPDHom E b D₁
      (deltaPDCompletionStructure_isPerfect _ (deltaPerfection_isPerfect G) y)
      r₁ (((pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom G 0)).comp
        (pdCompletionUnit_isDeltaHom E b))
      (pdCompletionH0_self_complete_p P p y) (pdCompletionH0_self_complete_d P p y)
    apply (hu₁ (f.comp g) ⟨hf.1.comp hg.1, ?_⟩).trans
      (hu₁ (RingHom.id H₁) ⟨(D₁).isDeltaHom_id, RingHom.id_comp r₁⟩).symm
    rw [RingHom.comp_assoc, hg.2, hf.2]
  exact RingEquiv.ofRingHom f g hfg hgf

/-- この環同型の両方向はδ射であり、元の標準raw射を保つ。 -/
theorem deltaPDCompletionPerfectionEquiv_spec :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (D₀).IsDeltaHom D₁ (deltaPDCompletionPerfectionEquiv E b).toRingHom ∧
      (D₁).IsDeltaHom D₀ (deltaPDCompletionPerfectionEquiv E b).symm.toRingHom ∧
      (deltaPDCompletionPerfectionEquiv E b).toRingHom.comp r₀ = r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact ⟨(deltaPDCompletionPerfectionComparison_spec E b).1,
    (deltaPDCompletionPerfectionInverse_spec E b).1,
    (deltaPDCompletionPerfectionComparison_spec E b).2⟩

/-- 同じ標準環同型は、元の元bの両完備化後の像を保つ。 -/
theorem deltaPDCompletionPerfectionEquiv_generator :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    deltaPDCompletionPerfectionEquiv E b (pdCompletionUnit C p x x) =
      pdCompletionUnit P p y y := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact RingHom.congr_fun (deltaPDCompletionPerfectionEquiv_spec E b).2.2 b

/-- 両手順の同じ標準生成元商も、元の標準環同型により同型。 -/
def deltaPDCompletionPerfectionQuotientEquiv :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (H₀ ⧸ Ideal.span {(pdCompletionUnit C p x x)}) ≃+*
      (H₁ ⧸ Ideal.span {(pdCompletionUnit P p y y)}) := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  exact Ideal.quotientEquiv _ _ (deltaPDCompletionPerfectionEquiv E b) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(pdCompletionUnit P p y y)} =
      Ideal.span {(deltaPDCompletionPerfectionEquiv E b (pdCompletionUnit C p x x))}
    rw [deltaPDCompletionPerfectionEquiv_generator])

/-- 商環同型は、各代表元に両手順の標準環同型を適用する。 -/
theorem deltaPDCompletionPerfectionQuotientEquiv_mk :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    ∀ h : H₀, deltaPDCompletionPerfectionQuotientEquiv E b (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (deltaPDCompletionPerfectionEquiv E b h) := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  intro h
  rfl

/-- 商比較も、元Bからの両標準係数射を保つ。 -/
theorem deltaPDCompletionPerfectionQuotientEquiv_comp_raw :
    letI := pdCompletionCommRing B p b
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing P p y
    (deltaPDCompletionPerfectionQuotientEquiv E b).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit C p x x)})).comp r₀) =
      (Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)})).comp r₁ := by
  let := pdCompletionCommRing B p b
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing P p y
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)})
    (deltaPDCompletionPerfectionEquiv E b (r₀ a)) =
      Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)}) (r₁ a)
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(pdCompletionUnit P p y y)}))
    (RingHom.congr_fun (deltaPDCompletionPerfectionEquiv_spec E b).2.2 a)

end SerrePositivity.BhattScholze
