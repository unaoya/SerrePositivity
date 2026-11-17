module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechPullbackAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback

/-!
概要：細分を含む実際の Frobenius 係数の引き戻しは、スカラーの増大写像を保つ。
方針：逆像への引き戻しと、細分での増大写像の自然性を合成する。
規約：同じ大域スカラーと余鎖写像を保持し、平坦性を仮定しない。
使われ方：表示の同型の三角形による四角形の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

set_option backward.isDefEq.respectTransparency false in
/-- 同じスカラーに沿う refinedPullback の零次は、同じ native な増大写像と可換。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_augmentation
    (f : X ⟶ Y) (φ : R →+* Γ(Y, ⊤)) (ψ : R →+* Γ(X, ⊤))
    (hψ : ψ = f.appTop.hom.comp φ)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    (U : ι → Y.Opens) (V : κ → X.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j)) :
    ((schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ).f 0).hom.comp
        (schemeStructurePerfectCechAugmentation Y φ p hp hR hY U) =
      schemeStructurePerfectCechAugmentation X ψ p hp hR hX V := by
  change (((openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
    (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ).f 0).hom.comp
      ((schemeStructurePerfectCechPullbackMap f p hp hY hX U).f 0).hom).comp _ = _
  rw [LinearMap.comp_assoc,
    schemeStructurePerfectCechPullbackMap_augmentation f φ ψ hψ p hp hR hY hX U]
  exact schemeStructurePerfectCechAugmentation_refinement X ψ p hp hR hX
    (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ

end SerrePositivity.AlgebraicGeometry
