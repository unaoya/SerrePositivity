module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 共役の不変性の実ホモトピー

概要：離散群の u⁻¹hu 共役と恒等写像の間の自然変換と nerve の実ホモトピーを作る。
方針：一対象群圏の自然変換の成分を u⁻¹ とする。
規約：KST Construction A.6 の共役の向きを保つ。
使われ方：群ホモロジーの共役不変性と Lemma 4.16 の同変ホモトピー。
-/

universe u v w c
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {H : Type u} [Group H]

/-- 概要：元 u による h↦u⁻¹hu の共役準同型。
方針：積の中の u*u⁻¹ を相殺する。
規約：原典の向き u⁻¹hu。使われ方：KST Construction A.6 の φ_u。 -/
def inverseConjugation (u : H) : H →* H where
  toFun h := u⁻¹ * h * u
  map_one' := by simp
  map_mul' a b := by simp [mul_assoc]

/-- 概要：共役準同型が一対象群圏に誘導する関手。
方針：SingleObj の準同型による関手を使う。
規約：対象は唯一。使われ方：KST Construction A.6 の自然変換の標的。 -/
def conjugationFunctor (u : H) : SingleObj H ⥤ SingleObj H :=
  SingleObj.mapHom H H (inverseConjugation u)

/-- 概要：恒等関手から共役関手への成分 u⁻¹ の自然変換。
方針：u⁻¹h=(u⁻¹hu)u⁻¹ を使う。
規約：KST Construction A.6 の原典と同じ向き。
使われ方：nerve 上の恒等写像と共役の実ホモトピー。 -/
def conjugationNaturalTransformation (u : H) :
    𝟭 (SingleObj H) ⟶ conjugationFunctor u where
  app _ := u⁻¹
  naturality _ _ h := by
    change u⁻¹ * h = (u⁻¹ * h * u) * u⁻¹
    simp [mul_assoc]

/-- 概要：離散群の分類空間上の恒等写像と共役の実単体的ホモトピー。
方針：成分 u⁻¹ の自然変換を nerve のホモトピーへ送る。
規約：群の可換性は要求しない。使われ方：KST Construction A.6 の C(H) への移送の入力。 -/
def conjugationNerveHomotopy (u : H) :
    SSet.Homotopy (nerveMap (𝟭 (SingleObj H))) (nerveMap (conjugationFunctor u)) :=
  SerrePositivity.NerveHomotopy.homotopy (conjugationNaturalTransformation u)

/-- 概要：共役準同型の構成は準同型による元の移送に自然。
方針：準同型の積と逆元の保存を使う。
規約：任意の群準同型。使われ方：KST Construction A.6 の (H,u) についての関手性。 -/
theorem inverseConjugation_naturality {H' : Type v} [Group H'] (f : H →* H') (u : H) :
    f.comp (inverseConjugation u) = (inverseConjugation (f u)).comp f := by
  ext h
  change f (u⁻¹ * h * u) = (f u)⁻¹ * f h * f u
  rw [map_mul, map_mul, map_inv]

/-- 概要：自然変換の成分も準同型による元の移送に自然。
方針：準同型の逆元保存を使う。
規約：自然変換を元ごとの式で比較する。
使われ方：KST Construction A.6 のホモトピーの標準性。 -/
theorem conjugationNaturalTransformation_naturality {H' : Type v} [Group H']
    (f : H →* H') (u : H) : f ((conjugationNaturalTransformation u).app (SingleObj.star H)) =
      (conjugationNaturalTransformation (f u)).app (SingleObj.star H') :=
  map_inv f u

/-- 概要：共役と恒等写像が誘導する鎖写像の間の実鎖ホモトピー。
方針：一対象群圏の nerve のホモトピーを、係数付き自由鎖複体へ送る。
規約：係数対象 R は任意。H_* の所有レーンの定義を置き換えない。
使われ方：KST Construction A.6 の C(H) の鎖模型と正規化への移送。 -/
def conjugationChainHomotopy {C : Type w} [Category.{c} C]
    [Preadditive C] [CategoryTheory.Limits.HasCoproducts.{u} C] (R : C) (u : H) :
    Homotopy (SSet.chainComplexMap (nerveMap (𝟭 (SingleObj H))) R)
      (SSet.chainComplexMap (nerveMap (conjugationFunctor u)) R) :=
  (conjugationNerveHomotopy u).chainComplexMap R

/-- 概要：共役と恒等写像の間の非被約 C(H) のテンソル区間ホモトピー。
方針：成分 u⁻¹ の自然変換の nerve ホモトピーを自由化し、積とテンソルの同型で移す。
規約：KST Construction A.6、Definition A.3 の両端条件を全次数で満たす。
使われ方：Lemma 4.16 の C(ψ) の比較と任意の m 次への制限。 -/
def conjugationLinearizedHomotopy (u : H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (𝟭 (SingleObj H))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (conjugationFunctor u))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedTensorHomotopy (conjugationNerveHomotopy u)

end SerrePositivity.KST.ProExcision
