module
public import SerrePositivity.DifferentialGraded.Tensor.QuadElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponent

/-! # 五角の二辺からなる経路の四重生成元上の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma pentagonShort_component_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s i m l j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n)
    (hl : a + k = l) (hj : l + r = j) :
    associatorValueComponent A B C E G P Q (compose A E F G R S) b g n
      (associatorValueComponent A B E F G (compose A B C E P Q) R S b g n
        (quadLeftElement A B C E F G P Q R S b c e f g σ τ q v hi hm hn)) =
    quadRightElement A B C E F G P Q R S b c e f g σ τ q v hl hj (by omega) := by
  have h₁ := associatorValueComponent_element A B E F G (compose A B C E P Q) R S b e f g
    (k := a) (r := k) (s := i) (i := m) (l := l) (n := n) σ τ
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm hl hn
  have h₂ := associatorValueComponent_element A B C E G P Q (compose A E F G R S) b c e g
    (k := l) (r := r) (s := s) (i := i) (l := j) (n := n)
    (BalancedTensor.element A F (S.rightAt g) (R.leftAt e) f σ τ hl) q v hi hj (by omega)
  exact (congrArg (associatorValueComponent A B C E G P Q (compose A E F G R S) b g n) h₁).trans h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
