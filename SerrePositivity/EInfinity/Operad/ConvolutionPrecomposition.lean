module

public import SerrePositivity.EInfinity.Operad.ConvolutionOperations
public import SerrePositivity.EInfinity.Operad.ConvolutionAssemblyPrecomposition

/-!
# 余代数射による convolution の前合成

概要：Berger–Fresse §3.1 の convolution 演算は始域の余代数射と両立する。
方針：反復評価の前合成の自然性と余代数射の保存則を組み立ての自然性へ渡す。
規約：全 arity について演算の保存を証明する。
使われ方：区間の端点・収縮の前合成を代数射へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：評価後の convolution は余代数射の前合成について自然（BF §3.1）。
方針：余代数射の余演算保存と反復評価の前合成の自然性を適用する。
規約：値域の代数は固定する。
使われ方：転置後の前合成の演算保存を導く。 -/
lemma convolutionUncurriedAction_pre (hP : Hopf P) {H H' : P.Coalgebra}
    (f : H' ⟶ H) (B : P.Algebra) (n : ℕ) :
    ((P.arity n ◁ TensorPowers.map (homPrecompose f.hom B.carrier) n) ▷ H'.carrier) ≫
      convolutionUncurriedAction hP H' B n =
    ((P.arity n ⊗ power (homComplex A H.carrier B.carrier) n) ◁ f.hom) ≫
      convolutionUncurriedAction hP H B n := by
  have hn := convolutionAssembly_pre
    (hP.diagonal.map.app (FiniteBijection.of n)) (H.coaction n)
    (convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (H'.coaction n) (convolutionPowerEvaluation H'.carrier B.carrier n)
    (TensorPowers.map (homPrecompose f.hom B.carrier) n) f.hom (TensorPowers.map f.hom n)
    (f.comm n) (convolutionPowerEvaluation_pre f.hom B.carrier n)
  convert hn using 1 <;> rfl

/-- 概要：余代数射の前合成は convolution の全演算を保つ（BF §3.1）。
方針：右転置の入力と Hom の始域の自然性で評価後の等式を戻す。
規約：余代数射は任意でよい。
使われ方：端点・収縮からの代数射と convolution の反変性を構成する。 -/
lemma convolutionAction_pre (hP : Hopf P) {H H' : P.Coalgebra}
    (f : H' ⟶ H) (B : P.Algebra) (n : ℕ) :
    convolutionAction hP H B n ≫ homPrecompose f.hom B.carrier =
    (P.arity n ◁ TensorPowers.map (homPrecompose f.hom B.carrier) n) ≫
      convolutionAction hP H' B n := by
  simp only [convolutionAction]
  rw [← curryRight_naturality_domain, ← curryRight_naturality_source,
    tensorHom_id, id_tensorHom, convolutionUncurriedAction_pre]

end SerrePositivity.EInfinity.Operad
