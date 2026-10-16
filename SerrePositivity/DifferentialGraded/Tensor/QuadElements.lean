module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # 四つのbimoduleの両端括弧付けにおける四重斉次生成元 -/
@[expose] public section
noncomputable section
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 合成の完全左括弧付け（値はS⊗(R⊗(Q⊗P))）の四重生成元。 -/
def quadLeftElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s i m n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) :
    ((compose A B F G (compose A B E F (compose A B C E P Q) R) S).value b g).X n :=
  BalancedTensor.element A F (S.rightAt g)
    ((compose A B E F (compose A B C E P Q) R).leftAt b) f σ
    (associatorLeftElement A B C E F P Q R b c e f τ q v hi hm) hn

/-- 合成の完全右括弧付け（値は((S⊗R)⊗Q)⊗P）の四重生成元。 -/
def quadRightElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s l j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : a + k = l) (hj : l + r = j) (hn : j + s = n) :
    ((compose A B C G P (compose A C E G Q (compose A E F G R S))).value b g).X n :=
  BalancedTensor.element A C ((compose A C E G Q (compose A E F G R S)).rightAt g)
    (P.leftAt b) c (associatorRightElement A C E F G Q R S c e f g σ τ q hl hj) v hn

/-- 五角の長い経路の中間（値は(S⊗(R⊗Q))⊗P）の生成元。 -/
def quadMiddleElement (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G)
    (b : B) (c : C) (e : E) (f : F) (g : G) {a k r s z j n : ℤ}
    (σ : (S.value f g).X a) (τ : (R.value e f).X k)
    (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hz : k + r = z) (hj : a + z = j) (hn : j + s = n) :
    ((compose A B C G P (compose A C F G (compose A C E F Q R) S)).value b g).X n :=
  BalancedTensor.element A C ((compose A C F G (compose A C E F Q R) S).rightAt g)
    (P.leftAt b) c (associatorLeftElement A C E F G Q R S c e f g σ τ q hz hj) v hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
