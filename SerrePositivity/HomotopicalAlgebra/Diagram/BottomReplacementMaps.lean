module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacement

/-! # Comparison maps for replacement of the least diagram value -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.BottomReplacement
variable {K : Type w} [PartialOrder K] [OrderBot K] {C : Type u} [Category.{v} C]
  {X : C} {U V : K ⥤ C} (a : (Functor.const K).obj X ⟶ U)

local instance : DecidableEq K := Classical.decEq K

def comparisonApp (k : K) : obj a k ⟶ U.obj k := by
  by_cases h : k = ⊥
  · exact (botIso a k h).hom ≫ a.app k
  · exact (awayIso a k h).hom

def comparison : diagram a ⟶ U where
  app := comparisonApp a
  naturality i j f := by
    by_cases hj : j = ⊥
    · have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
      subst i
      subst j
      have hf : f = 𝟙 (⊥ : K) := Subsingleton.elim _ _
      subst f
      simp [diagram, comparisonApp]
    · by_cases hi : i = ⊥
      · have hn := a.naturality f
        change 𝟙 X ≫ a.app j = a.app i ≫ U.map f at hn
        simp only [Category.id_comp] at hn
        simpa [diagram, map, comparisonApp, hi, hj, Category.assoc] using hn
      · simp [diagram, map, comparisonApp, hi, hj, Category.assoc]

variable (c : (Functor.const K).obj X ⟶ V) (p : U ⟶ V) (h : a ≫ p = c)

def changeApp (k : K) : obj a k ⟶ obj c k := by
  by_cases hk : k = ⊥
  · exact (botIso a k hk).hom ≫ (botIso c k hk).inv
  · exact (awayIso a k hk).hom ≫ p.app k ≫ (awayIso c k hk).inv

def change (h : a ≫ p = c) : diagram a ⟶ diagram c where
  app := changeApp a c p
  naturality i j f := by
    by_cases hj : j = ⊥
    · have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
      simp [diagram, map, changeApp, hi, hj, Category.assoc]
    · by_cases hi : i = ⊥
      · have hn := congr_app h j
        change a.app j ≫ p.app j = c.app j at hn
        simpa [diagram, map, changeApp, hi, hj, Category.assoc] using
          congrArg (fun t => t ≫ (awayIso c j hj).inv) hn
      · simp [diagram, map, changeApp, hi, hj, Category.assoc]

include h in
lemma comparison_change : comparison a ≫ p = change a c p h ≫ comparison c := by
  apply NatTrans.ext
  funext k
  have hn := congr_app h k
  change a.app k ≫ p.app k = c.app k at hn
  change comparisonApp a k ≫ p.app k = changeApp a c p k ≫ comparisonApp c k
  by_cases hk : k = ⊥
  · simpa only [comparisonApp, changeApp, dite_eq_left hk, Category.assoc,
      Iso.inv_hom_id_assoc] using congrArg (fun t => (botIso a k hk).hom ≫ t) hn
  · simp only [comparisonApp, changeApp, dite_eq_right hk, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.DiagramModel.BottomReplacement
