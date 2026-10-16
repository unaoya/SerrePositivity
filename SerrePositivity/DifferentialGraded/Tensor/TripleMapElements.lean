module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
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

lemma leftTripleMap_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s i n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    (composeValueMap A B E F (composeMap A B C E f g) h b d).f n
      (associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hi hn) =
    associatorLeftElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hi hn := by
  let x := BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b) c q v hi
  have ho := composeValueMap_element A B E F (composeMap A B C E f g) h b e d τ x hn
  have hv := congrArg (fun z :
      (compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).value b e ⟶
      (compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).value b e => z.f i x)
    (composeMap_value_eval A B C E f g b e)
  have hi₀ := hv.trans (composeValueMap_element A B C E f g b c e q v hi)
  exact ho.trans (congrArg (fun z :
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).value b e).X i =>
    BalancedTensor.element A E ((BimoduleCategory.underlying A E F R').rightAt d)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) e
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ) z hn) hi₀)

lemma rightTripleMap_element (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (c : C) (e : E) (d : F) {k r s l n : ℤ}
    (τ : ((BimoduleCategory.underlying A E F R).value e d).X k)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    (composeValueMap A B C F f (composeMap A C E F g h) b d).f n
      (associatorRightElement A B C E F (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)
        b c e d τ q v hl hn) =
    associatorRightElement A B C E F (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') b c e d
      (((BimoduleCategory.valueEvaluation A E F e d).map h).f k τ)
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r q)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hl hn := by
  let x := BalancedTensor.element A E ((BimoduleCategory.underlying A E F R).rightAt d)
    ((BimoduleCategory.underlying A C E Q).leftAt c) e τ q hl
  have ho := composeValueMap_element A B C F f (composeMap A C E F g h) b c d x v hn
  have hv := congrArg (fun z :
      (compose A C E F (BimoduleCategory.underlying A C E Q)
        (BimoduleCategory.underlying A E F R)).value c d ⟶
      (compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).value c d => z.f l x)
    (composeMap_value_eval A C E F g h c d)
  have hi₀ := hv.trans (composeValueMap_element A C E F g h c e d τ q hl)
  exact ho.trans (congrArg (fun z :
      ((compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).value c d).X l =>
    BalancedTensor.element A C
      ((compose A C E F (BimoduleCategory.underlying A C E Q')
        (BimoduleCategory.underlying A E F R')).rightAt d)
      ((BimoduleCategory.underlying A B C P').leftAt b) c z
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s v) hn) hi₀)

end SerrePositivity.DifferentialGraded.BimoduleTensor
