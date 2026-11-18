module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnitSource
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraIntervalUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionPathComplex

/-!
模型。文献の定義との比較は後で
# 余代数区間に付随する代数の prepath object

概要：Berger–Moerdijk 命題 4.1、Berger–Fresse §3.1 の代数の定数射と端点評価を構成する。
方針：区間からの convolution 関手に単位余代数との自然な代数同型を接続する。
規約：この段階ではモデル的な fibration と弱同値の性質は要求しない。
使われ方：転送に必要な全代数の functorial path object の代数としてのデータとなる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：区間からの convolution は P 代数の自己関手（BF §3.1）。
方針：固定した区間の余代数からの convolution 関手を用いる。
規約：区間の augmentation は Hopf 余単位。
使われ方：functorial path object の代数の本体となる。 -/
def algebraPathFunctor (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    P.Algebra ⥤ P.Algebra := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionFunctor hP I.coalgebra

/-- 概要：定数関数への射は自然な P 代数射（BF §3.1）。
方針：単位余代数との比較の逆射の後で区間の収縮を前合成する。
規約：底の射は既存の constant と同じ。
使われ方：代数の prepath object の第一射となる。 -/
def algebraConstantNat (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    𝟭 P.Algebra ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraPathFunctor hP I :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUnitNatIso hP).inv ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPreNat hP I.contractionHom

/-- 概要：指定端点での評価は自然な P 代数射（BF §3.1）。
方針：区間の端点を前合成して単位余代数との比較を適用する。
規約：両端点を同じ自然変換の族で扱う。
使われ方：代数の prepath object の二つの評価射となる。 -/
def algebraEvaluationNat (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraPathFunctor hP I ⟶ 𝟭 P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPreNat hP (I.endpointHom b) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUnitNatIso hP).hom

/-- 概要：代数の定数射の底は既存の複体の定数射（BF §3.1）。
方針：前合成と標準の単位同型の定義を比較する。
規約：厳密な chain map の等式。
使われ方：モデル的な性質を底の複体から移す。 -/
lemma algebraConstantNat_hom (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat hP I).app B).hom = I.constant B.carrier := rfl

/-- 概要：代数の端点評価の底は既存の複体の評価射（BF §3.1）。
方針：端点の前合成と標準の単位同型の定義を比較する。
規約：両端点について厳密な chain map の等式。
使われ方：評価の fibration 性を底の複体で検証する。 -/
lemma algebraEvaluationNat_hom (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) (b : Bool) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I b).app B).hom = I.evaluation B.carrier b := rfl

/-- 概要：区間から全ての P 代数の prepath object を得る（BM 命題 4.1）。
方針：自然な定数射・両端点評価と底での三角形を束ねる。
規約：cofibrancy を要求せず、モデル的性質は後続で検証する。
使われ方：fibrations.llp に属する射の底のホモトピー同値性を示す。 -/
def prepathAlgebra (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) (B : P.Algebra) :
    HomotopicalAlgebra.PrepathObject B where
  P := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraPathFunctor hP I).obj B
  ι := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat hP I).app B
  p₀ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I false).app B
  p₁ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I true).app B
  ι_p₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat hP I).app B).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I false).app B).hom = 𝟙 B.carrier
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat_hom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat_hom]
    exact I.constant_evaluation B.carrier false
  ι_p₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat hP I).app B).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I true).app B).hom = 𝟙 B.carrier
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat_hom, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat_hom]
    exact I.constant_evaluation B.carrier true

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
