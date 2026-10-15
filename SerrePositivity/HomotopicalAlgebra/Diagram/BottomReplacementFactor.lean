module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacementMaps

/-! # Factorization through a diagram with prescribed bottom value -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.BottomReplacement
variable {K : Type w} [PartialOrder K] [OrderBot K] {C : Type u} [Category.{v} C]
  {D V : K ⥤ C} (b : D ⟶ V)

local instance : DecidableEq K := Classical.decEq K

abbrev based := ContinuousLifts.fromBottom D ≫ b

def factorApp (k : K) : D.obj k ⟶ obj (based b) k := by
  by_cases hk : k = ⊥
  · exact eqToHom (congrArg D.obj hk) ≫ (botIso (based b) k hk).inv
  · exact b.app k ≫ (awayIso (based b) k hk).inv

def factor : D ⟶ diagram (based b) where
  app := factorApp b
  naturality i j f := by
    by_cases hj : j = ⊥
    · have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
      subst i
      subst j
      have hf : f = 𝟙 (⊥ : K) := Subsingleton.elim _ _
      subst f
      simp [diagram, factorApp]
    · by_cases hi : i = ⊥
      · subst i
        have hf : f = homOfLE (bot_le : (⊥ : K) ≤ j) := Subsingleton.elim _ _
        subst f
        simp [diagram, map, factorApp, hj, based, ContinuousLifts.fromBottom,
          Category.assoc]
      · simp [diagram, map, factorApp, hi, hj, Category.assoc]

lemma factor_comparison : factor b ≫ comparison (based b) = b := by
  apply NatTrans.ext
  funext k
  change factorApp b k ≫ comparisonApp (based b) k = b.app k
  by_cases hk : k = ⊥
  · subst k
    simp [factorApp, comparisonApp, based, ContinuousLifts.fromBottom]
  · simp [factorApp, comparisonApp, hk, Category.assoc]

lemma factor_bot_comp :
    (factor b).app ⊥ ≫ (botIso (based b) ⊥ rfl).hom = 𝟙 (D.obj ⊥) := by
  change factorApp b ⊥ ≫ (botIso (based b) ⊥ rfl).hom = _
  simp [factorApp]

variable {X : C} {U : K ⥤ C} (a : (Functor.const K).obj X ⟶ U)
  (c : (Functor.const K).obj X ⟶ V) (p : U ⟶ V) (h : a ≫ p = c)

lemma change_bot_comp :
    (change a c p h).app ⊥ ≫ (botIso c ⊥ rfl).hom = (botIso a ⊥ rfl).hom := by
  change changeApp a c p ⊥ ≫ (botIso c ⊥ rfl).hom = _
  simp [changeApp, Category.assoc]

lemma comparison_bot :
    (comparison a).app ⊥ = (botIso a ⊥ rfl).hom ≫ a.app ⊥ := by
  change comparisonApp a ⊥ = _
  simp [comparisonApp]

end SerrePositivity.DiagramModel.BottomReplacement
