module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassMap

/-!
概要：等しい実係数射の別表示へ、元の class 証人と模型射を全射を保って移す。
方針：始点の等式だけを移し、元の経路の射と模型射の同定を使う。
規約：係数の等式を入力する。使われ方：fixed 模型合成を直接分母係数で表示する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m m' : M ⟶ N) (h : m = m')
  (a : W ⟶ SquareZero.algebra A M) (b : W ⟶ SquareZero.algebra A N) {q : W ⟶ A}
  (v : SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m) b)

def changeCoefficientWitness :
    SquareZero.RelativeWitness q N (a ≫ SquareZero.coefficientMap A m') b where
  hom := v.hom
  source_eq := v.source_eq.trans (congrArg (fun t => a ≫ SquareZero.coefficientMap A t) h)
  target_eq := v.target_eq
  projection_eq := v.projection_eq

lemma changeCoefficientWitness_hom : (changeCoefficientWitness m m' h a b v).hom = v.hom := rfl

lemma classModelMap_changeCoefficient : classModelMap m a b v =
    classModelMap m' a b (changeCoefficientWitness m m' h a b v) := by
  subst m'
  apply classModelMap_congr
  rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
