module

public import SerrePositivity.HomotopicalAlgebra.Smith.PresentableWeakReflection

/-! # The actual generated factorization as a weak reflection

Its right arrow factor takes values in the original generated right class.
Every square into that class extends across the unit by a genuine lift.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.GeneratedWeakReflection
variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)
  (d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp)

abbrev rightFactor := AccessibleFactorization.rightFactor d

def unit : 𝟭 (Arrow C) ⟶ rightFactor I d where
  app f := Arrow.homMk (d.i.app f) (𝟙 _) (by
    change d.i.app f ≫ d.p.app f = f.hom ≫ 𝟙 _
    rw [d.fac_app, Category.comp_id])
  naturality f g φ := by
    apply Arrow.hom_ext
    · exact d.i.naturality φ
    · change φ.right ≫ 𝟙 _ = 𝟙 _ ≫ φ.right
      simp

lemma factor {f p : Arrow C} (hp : I.rlp p.hom) (φ : f ⟶ p) :
    ∃ ψ : (rightFactor I d).obj f ⟶ p, (unit I d).app f ≫ ψ = φ := by
  have : HasLiftingProperty (d.i.app f) p.hom := d.hi f _ hp
  let sq : CommSq φ.left (d.i.app f) p.hom (d.p.app f ≫ φ.right) := ⟨by
    rw [← Category.assoc, d.fac_app]
    exact φ.w⟩
  refine ⟨Arrow.homMk sq.lift φ.right sq.fac_right, ?_⟩
  apply Arrow.hom_ext
  · change d.i.app f ≫ sq.lift = φ.left
    exact sq.fac_left
  · change 𝟙 _ ≫ φ.right = φ.right
    exact Category.id_comp _

/-- The only extra hypothesis here is preservation of presentable objects;
accessibility of the generated factorization is supplied separately by A0. -/
def presentableReflection (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [(rightFactor I d).PreservesCardinalPresentable κ] :
    PresentableWeakReflection (arrowProperty I.rlp) κ where
  R := rightFactor I d
  unit := unit I d
  obj_mem f := d.hp f
  preservesPresentable := inferInstance
  factor hp φ := factor I d hp φ

end SerrePositivity.Smith.GeneratedWeakReflection
