module

public import SerrePositivity.EInfinity.Operad.ConvolutionOperations
public import SerrePositivity.EInfinity.Operad.ConvolutionAssembly

/-!
# 代数射による convolution の後合成

概要：Berger–Fresse §3.1 の convolution 演算は値域の P 代数射と両立する。
方針：反復評価の後合成の自然性と、代数射の演算保存を組み立ての自然性へ渡す。
規約：ここでは各演算の保存を証明し、代数への束ねは合成公理の後に行う。
使われ方：convolution の関手性と functorial path object の値域の射を構成する。
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

/-- 概要：評価後の convolution は値域の代数射について自然（BF §3.1）。
方針：入力関数への後合成を反復評価から出力の射へ移す。
規約：余代数は固定し、全 arity の演算を扱う。
使われ方：転置後の後合成の演算保存を導く。 -/
lemma convolutionUncurriedAction_post (hP : Hopf P) (H : P.Coalgebra)
    {B B' : P.Algebra} (f : B ⟶ B') (n : ℕ) :
    ((P.arity n ◁ TensorPowers.map (homPostcompose H.carrier f.hom) n) ▷ H.carrier) ≫
      convolutionUncurriedAction hP H B' n = convolutionUncurriedAction hP H B n ≫ f.hom := by
  have ha : (P.arity n ◁ TensorPowers.map f.hom n) ≫ B'.action n =
      B.action n ≫ f.hom := by
    simpa only [id_tensorHom] using (f.comm n).symm
  have hn := convolutionAssembly_post
    (hP.diagonal.map.app (FiniteBijection.of n)) (H.coaction n)
    (convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (convolutionPowerEvaluation H.carrier B'.carrier n) (B'.action n)
    (TensorPowers.map (homPostcompose H.carrier f.hom) n) (TensorPowers.map f.hom n) f.hom
    (convolutionPowerEvaluation_post H.carrier f.hom n) ha
  convert hn using 1 <;> rfl

/-- 概要：内部 Hom の後合成は全ての convolution 演算を保つ（BF §3.1）。
方針：右転置の値域・入力の自然性で評価後の自然性を戻す。
規約：P 代数の合成公理を追加仮定にしない。
使われ方：convolution 代数の後合成関手の演算保存条件となる。 -/
lemma convolutionAction_post (hP : Hopf P) (H : P.Coalgebra)
    {B B' : P.Algebra} (f : B ⟶ B') (n : ℕ) :
    convolutionAction hP H B n ≫ homPostcompose H.carrier f.hom =
      (P.arity n ◁ TensorPowers.map (homPostcompose H.carrier f.hom) n) ≫
        convolutionAction hP H B' n := by
  simp only [convolutionAction]
  rw [← curryRight_naturality_target,
    ← curryRight_naturality_source, tensorHom_id, convolutionUncurriedAction_post]

end SerrePositivity.EInfinity.Operad
