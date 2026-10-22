module

public import SerrePositivity.EInfinity.Operad.AlgebraHomComposition
public import SerrePositivity.EInfinity.Operad.Commutative

/-!
# Com 代数射の零入力・二入力による判定

概要：零入力と二入力を保つ底の射は、全 arity の Com 作用を保つ。
方針：一入力は単位則、後続入力は二入力への部分合成で帰納する。
規約：元の底の射・全入力数を保持する。
使われ方：零次集中 Com 代数と元の H⁰ 可換代数の離散像との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Algebra
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

lemma commutative_action_one (X : (commutativeOperad A).Algebra) :
    X.action 1 = (λ_ (power X.carrier 1)).hom ≫ (oneIso X.carrier).hom := by
  have h := X.unit_action
  change (𝟙 (𝟙_ (Complex A)) ▷ power X.carrier 1) ≫ X.action 1 = _ at h
  simpa only [id_whiskerRight, Category.id_comp] using h

lemma commutative_actionHom_of_zero_two
    (X Y : (commutativeOperad A).Algebra) (f : X.carrier ⟶ Y.carrier)
    (h0 : X.action 0 ≫ f = (𝟙_ (Complex A) ◁ TensorPowers.map f 0) ≫ Y.action 0)
    (h2 : X.action 2 ≫ f = (𝟙_ (Complex A) ◁ TensorPowers.map f 2) ≫ Y.action 2)
    (n : ℕ) : X.action n ≫ f =
      (𝟙_ (Complex A) ◁ TensorPowers.map f n) ≫ Y.action n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    cases n with
    | zero =>
      rw [commutative_action_one, commutative_action_one, leftUnitor_naturality_assoc,
        oneIso_naturality]
      exact Category.assoc _ _ _
    | succ n =>
      have : IsIso ((commutativeOperad A).comp 1 (n + 1) (1 : Fin 2)) := by
        change IsIso (λ_ (𝟙_ (Complex A))).hom
        infer_instance
      have hc := actionHom_of_composition X Y f 1 (n + 1) (1 : Fin 2) h2 ih
      change X.action (1 + (n + 1)) ≫ f =
        (𝟙_ (Complex A) ◁ TensorPowers.map f (1 + (n + 1))) ≫ Y.action (1 + (n + 1)) at hc
      rw [show 1 + (n + 1) = n + 1 + 1 by omega] at hc
      exact hc

def commutativeHomOfZeroTwo
    (X Y : (commutativeOperad A).Algebra) (f : X.carrier ⟶ Y.carrier)
    (h0 : X.action 0 ≫ f = (𝟙_ (Complex A) ◁ TensorPowers.map f 0) ≫ Y.action 0)
    (h2 : X.action 2 ≫ f = (𝟙_ (Complex A) ◁ TensorPowers.map f 2) ≫ Y.action 2) : X ⟶ Y where
  hom := f
  comm n := by
    rw [id_tensorHom]
    exact commutative_actionHom_of_zero_two X Y f h0 h2 n

end SerrePositivity.EInfinity.Operad.Algebra
