module
public import SerrePositivity.DifferentialGraded.Tensor.TripleMapElements
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # 反復tensor mapの三重斉次生成元上の評価 -/
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

lemma leftTripleComponent_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    composeMapComponent A B E F (composeMap A B C E f g) h b d n
      (associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hi hn) =
    associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hn :=
  (composeMapComponent_eq A B E F (composeMap A B C E f g) h b d n _).trans
    (leftTripleMap_element A B C E F f g h b c e d τ q v hi hn)

lemma rightTripleComponent_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s l n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    composeMapComponent A B C F f (composeMap A C E F g h) b d n
      (associatorRightElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hl hn) =
    associatorRightElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hl hn :=
  (composeMapComponent_eq A B C F f (composeMap A C E F g h) b d n _).trans
    (rightTripleMap_element A B C E F f g h b c e d τ q v hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
