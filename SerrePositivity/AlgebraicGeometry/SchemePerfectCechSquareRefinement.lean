module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechSquare
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：実際のスカラーと Frobenius 係数を入れた四角形に、被覆の細分の射を入れる。
方針：両空間の実際の細分写像と、既存の引き戻し・増大写像の自然性を使う。
規約：基底と中心の係数を固定し、完全性を射の仮定にしない。
使われ方：有限アフィン共通細分に沿う F8 の完全性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable {X Y : Scheme.{u}} {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

set_option backward.isDefEq.respectTransparency false in
/-- 両空間の実際の細分写像を入れた、同じスカラーの四角形の射。 -/
def schemeStructurePerfectCechSquare_refinement
    (f : X ⟶ Y) (q : R →+* S) (φ : R →+* Γ(Y, ⊤)) (ψ : S →+* Γ(X, ⊤))
    (hφ : f.appTop.hom.comp φ = ψ.comp q)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) :
    CechAugmentedSquare.Map (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U)
      (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX V) where
  left := openCoverCechRefinementMap (frobeniusRingDiagram Y.presheaf p hp hY) U V ρ hρ
  right := openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
    (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
    (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le)
  base := LinearMap.id
  center := LinearMap.id
  restriction := (schemeStructurePerfectCechPullbackMap_refinement f p hp hY hX U V ρ hρ).symm
  scalar := by
    simpa only [schemeStructurePerfectCechSquare, LinearMap.comp_id] using
      schemeStructurePerfectCechAugmentation_refinement Y φ p hp hR hY U V ρ hρ
  quotient := by simp [schemeStructurePerfectCechSquare]
  center_naturality := by
    simpa only [schemeStructurePerfectCechSquare, LinearMap.comp_id] using
      schemeStructurePerfectCechAugmentation_refinement X ψ p hp hS hX
        (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
        (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le)

end SerrePositivity.AlgebraicGeometry
