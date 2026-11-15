module

public import SerrePositivity.AlgebraicGeometry.SchemeCechPullbackAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechAugmentation

/-!
概要：構造層の実際の Frobenius 係数の引き戻しは、スカラーの増大写像と可換。
方針：係数前層の増大写像の自然性と、実際の環準同型の合成則を使う。
規約：スカラーの整合性を明示し、平坦性を要求しない。
使われ方：閉中心の逆像被覆での射影四角形の可換性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 実際のスカラーと整合する引き戻しは、その Frobenius 係数の増大写像と可換。 -/
theorem schemeStructurePerfectCechPullbackMap_augmentation
    (f : X ⟶ Y) (φ : R →+* Γ(Y, ⊤)) (ψ : R →+* Γ(X, ⊤))
    (hψ : ψ = f.appTop.hom.comp φ)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0) (U : ι → Y.Opens) :
    ((schemeStructurePerfectCechPullbackMap f p hp hY hX U).f 0).hom.comp
        (schemeStructurePerfectCechAugmentation Y φ p hp hR hY U) =
      schemeStructurePerfectCechAugmentation X ψ p hp hR hX (fun i ↦ f ⁻¹ᵁ U i) := by
  dsimp only [schemeStructurePerfectCechAugmentation, schemeStructurePerfectCechPullbackMap]
  rw [← LinearMap.comp_assoc, schemeCechPullbackMap_augmentation, LinearMap.comp_assoc]
  congr 1
  apply LinearMap.ext
  intro x
  change frobeniusDirectLimitMap p hp (hY (op ⊤)) (hX (op ⊤)) f.appTop.hom
      (frobeniusDirectLimitMap p hp hR (hY (op ⊤)) φ x) =
    frobeniusDirectLimitMap p hp hR (hX (op ⊤)) ψ x
  rw [hψ]
  exact congrArg (fun m ↦ m x)
    (frobeniusDirectLimitMap_comp p hp hR (hY (op ⊤)) φ (hX (op ⊤)) f.appTop.hom)

end SerrePositivity.AlgebraicGeometry
