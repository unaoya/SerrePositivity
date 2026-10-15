module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousRelativeCofibrancy

/-! # Replacing the bottom value of an ordered diagram

A cone from X to U permits replacing U at the least index by X. The
comparison to U is an isomorphism away from the least index. This is a
categorical construction, without a model structure or continuity input.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.BottomReplacement
variable {K : Type w} [PartialOrder K] [OrderBot K] {C : Type u} [Category.{v} C]
  {X : C} {U : K ⥤ C} (a : (Functor.const K).obj X ⟶ U)

local instance : DecidableEq K := Classical.decEq K

def obj (_a : (Functor.const K).obj X ⟶ U) (k : K) : C := if k = ⊥ then X else U.obj k

def botIso (k : K) (h : k = ⊥) : obj a k ≅ X := eqToIso (by simp [obj, h])
def awayIso (k : K) (h : k ≠ ⊥) : obj a k ≅ U.obj k := eqToIso (by simp [obj, h])

def map {i j : K} (f : i ⟶ j) : obj a i ⟶ obj a j := by
  by_cases hj : j = ⊥
  · have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
    exact (botIso a i hi).hom ≫ (botIso a j hj).inv
  · by_cases hi : i = ⊥
    · exact (botIso a i hi).hom ≫ a.app j ≫ (awayIso a j hj).inv
    · exact (awayIso a i hi).hom ≫ U.map f ≫ (awayIso a j hj).inv

lemma map_id (i : K) : map a (𝟙 i) = 𝟙 (obj a i) := by
  by_cases hi : i = ⊥
  · simp [map, hi]
  · simp [map, hi]

lemma map_comp {i j k : K} (f : i ⟶ j) (g : j ⟶ k) :
    map a (f ≫ g) = map a f ≫ map a g := by
  by_cases hk : k = ⊥
  · have hj : j = ⊥ := le_antisymm (hk ▸ leOfHom g) bot_le
    have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
    simp [map, hj, hk, Category.assoc]
  · by_cases hj : j = ⊥
    · have hi : i = ⊥ := le_antisymm (hj ▸ leOfHom f) bot_le
      simp [map, hi, hj, hk, Category.assoc]
    · by_cases hi : i = ⊥
      · have hn := a.naturality g
        change 𝟙 X ≫ a.app k = a.app j ≫ U.map g at hn
        simp only [Category.id_comp] at hn
        have he := (congrArg (fun t => t ≫ (awayIso a k hk).inv) hn).trans
          (Category.assoc _ _ _)
        simpa [map, hi, hj, hk, Category.assoc] using he
      · simp [map, hi, hj, hk, Category.assoc, U.map_comp]

def diagram : K ⥤ C where
  obj := obj a
  map := map a
  map_id := map_id a
  map_comp := map_comp a

end SerrePositivity.DiagramModel.BottomReplacement
