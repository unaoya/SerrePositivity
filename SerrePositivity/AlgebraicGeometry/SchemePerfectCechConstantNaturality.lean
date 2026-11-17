module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechConstantAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback

/-!
概要：元の全次数の定数増大は、実際の引き戻しと細分に自然。
方針：各タプルで元のappLEの自然性とFrobenius順極限の合成を使う。
規約：同じ大域スカラーと元の複体の射を保持する。
使われ方：元のタプル被覆の全次数の増大を自然変換にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数増大は、同じスカラーを保つrefinedPullbackに全次数で自然。 -/
theorem schemeStructurePerfectCechConstantAugmentation_naturality
    (f : X ⟶ Y) (φ : R →+* Γ(Y, ⊤)) (ψ : R →+* Γ(X, ⊤))
    (hψ : ψ = f.appTop.hom.comp φ)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    (U : ι → Y.Opens) (V : κ → X.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j)) :
    schemeStructurePerfectCechConstantAugmentation Y φ p hp hR hY U ≫
        schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ =
      schemeStructurePerfectCechConstantAugmentation X ψ p hp hR hX V := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext t
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [schemeStructurePerfectCechRefinedPullbackMap_apply,
    schemeStructurePerfectCechConstantAugmentation_apply,
    schemeStructurePerfectCechConstantAugmentation_apply]
  let W := cechOpenIntersection U (cechTupleSupport (ρ ∘ t))
  let Z := cechOpenIntersection V (cechTupleSupport t)
  let hZ : Z ≤ f ⁻¹ᵁ W := schemeCechRefinedPullbackIntersection_le f U V ρ hρ t
  have hc : Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op ≫ f.appLE W Z hZ =
      f.appTop ≫ X.presheaf.map (homOfLE (show Z ≤ ⊤ from le_top)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  have he : (f.appLE W Z hZ).hom.comp
      ((Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom.comp φ) =
      (X.presheaf.map (homOfLE (show Z ≤ ⊤ from le_top)).op).hom.comp ψ := by
    rw [hψ]
    ext z
    exact congrArg (fun m ↦ m.hom (φ z)) hc
  have hm := congrArg (fun z ↦ z x) (frobeniusDirectLimitMap_comp p hp hR (hY (op W))
    ((Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom.comp φ)
    (hX (op Z)) (f.appLE W Z hZ).hom)
  rw [he] at hm
  exact hm

end SerrePositivity.AlgebraicGeometry
