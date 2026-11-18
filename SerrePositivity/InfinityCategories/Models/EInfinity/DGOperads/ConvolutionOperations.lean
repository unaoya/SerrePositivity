module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Coalgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HopfComponents
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEvaluation

/-!
模型。文献の定義との比較は後で
# 内部 Hom の convolution 演算

概要：Berger–Fresse §3.1 の P-coalgebra H と P-algebra B から Hom(H,B) の演算を作る。
方針：Hopf 対角で係数を分配し、H の余演算・同時評価・B の演算を順に適用する。
規約：ここでは chain map とその転置を構成し、代数公理は後続で検証する。
使われ方：E-coalgebra 区間からの functorial path object の演算成分となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：convolution 演算を H で評価した chain map（BF §3.1）。
方針：対角の第一係数を B の作用、第二係数を H の余作用に使う。
規約：Koszul 交換は tensorμ に含み、零入力の演算も構成する。
使われ方：右 tensor 転置により内部 Hom 上の演算を定義する。 -/
def convolutionUncurriedAction (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra) (n : ℕ) :
    (P.arity n ⊗ power (homComplex A H.carrier B.carrier) n) ⊗ H.carrier ⟶ B.carrier :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n) (H.coaction n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)

/-- 概要：内部 Hom 上の n 入力の convolution 演算（BF §3.1）。
方針：H の点で評価した演算を符号なしの右 tensor 転置で戻す。
規約：各演算は全次数で微分と可換な chain map。
使われ方：convolution 代数の作用のデータとなる。 -/
def convolutionAction (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra) (n : ℕ) :
    P.arity n ⊗ power (homComplex A H.carrier B.carrier) n ⟶
      homComplex A H.carrier B.carrier :=
  curryRight (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B n)

/-- 概要：convolution 演算の評価は指定した余演算・同時評価の合成に戻る（BF §3.1）。
方針：右 tensor 転置の逆演算の往復則を使う。
規約：鎖写像全体の等式であり次数零に限らない。
使われ方：代数公理を評価後の余演算・演算の合成則へ帰着する。 -/
lemma convolutionAction_uncurry (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra) (n : ℕ) :
    uncurryRight (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B n :=
  uncurryRight_curryRight _

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
