module
public import SerrePositivity.DifferentialGraded.Tensor.TripleMapComponents
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponent

/-! # 閉零bimodule射の三変数に関する結合比較の生成元自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "Q₁" => BimoduleCategory.underlying A C E Q'
local notation "R₀" => BimoduleCategory.underlying A E F R
local notation "R₁" => BimoduleCategory.underlying A E F R'

lemma associatorComponent_map_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i l n : ℤ}
    (τ : ((R₀).value e d).X k) (q : ((Q₀).value c e).X r) (v : ((P₀).value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E F P₁ Q₁ R₁ b d n
      (composeMapComponent A B E F (composeMap A B C E f g) h b d n
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hn)) =
    composeMapComponent A B C F f (composeMap A C E F g h) b d n
      (associatorValueComponent A B C E F P₀ Q₀ R₀ b d n
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hn)) := by
  have hS := leftTripleComponent_element A B C E F f g h b c e d τ q v hi hn
  have hA := associatorValueComponent_element A B C E F P₀ Q₀ R₀ b c e d
    (k := k) (r := r) (s := s) (i := i) (l := l) (n := n) τ q v hi hl hn
  have hB := associatorValueComponent_element A B C E F P₁ Q₁ R₁ b c e d
    (k := k) (r := r) (s := s) (i := i) (l := l) (n := n)
    (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
    (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hl hn
  have hR := rightTripleComponent_element A B C E F f g h b c e d
    (k := k) (r := r) (s := s) (l := l) (n := n) τ q v hl (by omega)
  exact element_square
    (associatorValueComponent A B C E F P₀ Q₀ R₀ b d n)
    (associatorValueComponent A B C E F P₁ Q₁ R₁ b d n)
    (composeMapComponent A B E F (composeMap A B C E f g) h b d n)
    (composeMapComponent A B C F f (composeMap A C E F g h) b d n)
    _ _ _ _ hS hA hB hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
