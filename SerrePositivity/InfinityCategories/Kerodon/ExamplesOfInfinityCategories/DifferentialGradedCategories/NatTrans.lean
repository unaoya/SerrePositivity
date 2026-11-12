module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTransSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # 厳密 dg 自然変換の単体的ホモトピー

概要：厳密 dg 自然変換から dg nerve の写像を結ぶ単体的ホモトピーを構成する。
方針：標準一単体を単調な二相の選択と読み、各有限部分集合に二相間の写像を使う。
規約：HA Construction 1.3.1.6。使われ方：導来 ∞ 圏の関手間のホモトピー。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded MonoidalCategory Opposite
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D E : Type v}
  [DGCategory A D] [DGCategory A E] {F G : DGFunctor A D E}
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：相が常に零のホモトピー単体は F による像。
方針：全成分で二相の定義の最初の分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの始端。 -/
lemma simplex_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) :
    η.simplex s (OrderHom.const _ (0 : Fin 2)) = s.map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (simplex_zero)


/-- 概要：相が常に一のホモトピー単体は G による像。
方針：全成分で二相の定義の最後の分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの終端。 -/
lemma simplex_one {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) :
    η.simplex s (OrderHom.const _ (1 : Fin 2)) = s.map G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (simplex_one)


/-- 概要：厳密 dg 自然変換は dg nerve と標準一単体の積からの写像を定める。
方針：各単体を二相で写し、引き戻しとの可換性を自然性に使う。
規約：HA Construction 1.3.1.6。使われ方：dg 関手の像の間の単体的ホモトピー。 -/
def homotopyMap : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E where
  app _ := ↾fun s => η.simplex s.1 (SSet.stdSimplex.objEquiv s.2).toOrderHom
  naturality _ _ f := by
    ext s
    exact η.simplex_pullback s.1 (SSet.stdSimplex.objEquiv s.2).toOrderHom f.unop.toOrderHom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (homotopyMap)


/-- 概要：構成した積からの写像の始端は F の dg nerve 写像。
方針：標準一単体の零端点を定値零相として計算する。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの始端条件。 -/
lemma homotopyMap_zero : SSet.ι₀ ≫ η.homotopyMap = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  ext n s
  exact η.simplex_zero s

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (homotopyMap_zero)


/-- 概要：構成した積からの写像の終端は G の dg nerve 写像。
方針：標準一単体の一端点を定値一相として計算する。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの終端条件。 -/
lemma homotopyMap_one : SSet.ι₁ ≫ η.homotopyMap = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G := by
  ext n s
  exact η.simplex_one s

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (homotopyMap_one)


/-- 概要：厳密 dg 自然変換は二つの dg nerve 写像の単体的ホモトピーを与える。
方針：積からの写像と両端点の計算を Mathlib のホモトピーにまとめる。
規約：HA Construction 1.3.1.6。使われ方：導来 ∞ 圏に誘導する関手のホモトピー。 -/
def homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) where
  h := η.homotopyMap
  h₀ := η.homotopyMap_zero
  h₁ := η.homotopyMap_one
  rel := by
    ext n s
    exact False.elim s.1.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (homotopy)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
