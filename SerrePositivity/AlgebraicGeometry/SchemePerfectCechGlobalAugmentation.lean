module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedAugmentation
public import SerrePositivity.AlgebraicGeometry.AffinePerfectCechAugmentation

/-!
概要：同じ refined pullback は大域切断の恒等スカラーの増大を保つ。
方針：既存のスカラーの増大の自然性に、大域切断の環を渡す。
規約：実際の Γ(f) の Frobenius 係数写像を保持する。
使われ方：大域切断と同じタプル複体との自然な接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ refined pullback は、大域切断からの増大を実際の Γ(f) に沿って移す。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_globalAugmentation
    (f : X ⟶ Y) (p : ℕ) (hp : p.Prime)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    (U : ι → Y.Opens) (V : κ → X.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j)) :
    ((schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ).f 0).hom.comp
        (schemeStructurePerfectCechAugmentation Y (RingHom.id Γ(Y, ⊤))
          p hp (hY (op ⊤)) hY U) =
      (schemeStructurePerfectCechAugmentation X (RingHom.id Γ(X, ⊤))
        p hp (hX (op ⊤)) hX V).comp
        (frobeniusDirectLimitMap p hp (hY (op ⊤)) (hX (op ⊤))
          f.appTop.hom).toAddMonoidHom.toIntLinearMap := by
  rw [schemeStructurePerfectCechRefinedPullbackMap_augmentation f
    (RingHom.id Γ(Y, ⊤)) f.appTop.hom (by rw [RingHom.comp_id])]
  rw [schemeStructurePerfectCechAugmentation_id]
  rfl

end SerrePositivity.AlgebraicGeometry
