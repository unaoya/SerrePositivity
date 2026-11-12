module

public import SerrePositivity.AlgebraicGeometry.AffineSectionAlgebraAugmentation

/-!
概要：大域スカラーが全射なら、アフィン被覆の切断部分代数へのスカラーも全射。
方針：空交叉を全空間と照合し、実際の代数の増大写像を合成する。
規約：部分代数への写像は既存の algebraMap そのもの。
使われ方：中心外で次数零の余核が消えることの接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) (φ : R →+* Γ(Y, ⊤))
variable {ι : Type} [LinearOrder ι] (U : ι → Y.Opens)

/-- 空交叉の切断代数へのスカラーは、大域スカラーが全射なら全射。 -/
theorem schemeSectionAlgebraCech_empty_scalar_surjective (hφ : Function.Surjective φ) :
    Function.Surjective
      (algebraMap R ((schemeSectionAlgebraCechDiagram Y φ U).obj ∅)) := by
  change Function.Surjective
    (((Y.presheaf.map (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)).op).hom).comp φ)
  have htop : cechOpenIntersection U ∅ = ⊤ := by simp [cechOpenIntersection]
  letI : IsIso (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)) := by
    exact homOfLE_isIso_of_eq le_top htop
  exact (ConcreteCategory.bijective_of_isIso
    (Y.presheaf.map (homOfLE (show cechOpenIntersection U ∅ ≤ ⊤ from le_top)).op)).2.comp hφ

/-- アフィン被覆の適合する切断代数へのスカラーは、大域スカラーが全射なら全射。 -/
theorem affineSchemeSectionAlgebra_scalar_surjective [IsAffine Y]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)
    (hφ : Function.Surjective φ) :
    Function.Surjective
      (algebraMap R (fullAlgebraCechEqualizer (schemeSectionAlgebraCechDiagram Y φ U))) := by
  intro x
  obtain ⟨a, ha⟩ := affineSchemeSectionAlgebraAugmentation_surjective φ U hU hcU x
  obtain ⟨r, hr⟩ := schemeSectionAlgebraCech_empty_scalar_surjective Y φ U hφ a
  refine ⟨r, ?_⟩
  rw [← fullAlgebraCechAugmentation_algebraMap, hr]
  exact ha

end SerrePositivity.AlgebraicGeometry
