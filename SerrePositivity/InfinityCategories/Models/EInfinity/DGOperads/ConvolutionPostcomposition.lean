module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionOperations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：評価後の convolution は値域の代数射について自然（BF §3.1）。
方針：入力関数への後合成を反復評価から出力の射へ移す。
規約：余代数は固定し、全 arity の演算を扱う。
使われ方：転置後の後合成の演算保存を導く。 -/
lemma convolutionUncurriedAction_post (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra)
    {B B' : P.Algebra} (f : B ⟶ B') (n : ℕ) :
    ((P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (homPostcompose H.carrier f.hom) n) ▷ H.carrier) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B' n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP H B n ≫ f.hom := by
  have ha : (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map f.hom n) ≫ B'.action n =
      B.action n ≫ f.hom := by
    simpa only [id_tensorHom] using (f.comm n).symm
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_post
    (hP.diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n)) (H.coaction n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B'.carrier n) (B'.action n)
    (_root_.SerrePositivity.TensorPowers.map (homPostcompose H.carrier f.hom) n) (_root_.SerrePositivity.TensorPowers.map f.hom n) f.hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_post H.carrier f.hom n) ha
  convert hn using 1 <;> rfl

/-- 概要：内部 Hom の後合成は全ての convolution 演算を保つ（BF §3.1）。
方針：右転置の値域・入力の自然性で評価後の自然性を戻す。
規約：P 代数の合成公理を追加仮定にしない。
使われ方：convolution 代数の後合成関手の演算保存条件となる。 -/
lemma convolutionAction_post (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra)
    {B B' : P.Algebra} (f : B ⟶ B') (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ≫ homPostcompose H.carrier f.hom =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (homPostcompose H.carrier f.hom) n) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B' n := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction]
  rw [← curryRight_naturality_target,
    ← curryRight_naturality_source, tensorHom_id, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction_post]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
