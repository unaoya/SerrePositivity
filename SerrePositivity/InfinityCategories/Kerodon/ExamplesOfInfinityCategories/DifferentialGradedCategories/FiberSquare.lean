module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberProjection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # 標準 fiber の四角形と join 錐

概要：二つの複体の射の差の fiber から、標準の二脚とホモトピーを持つ四角形を構成する。
方針：mapping cone の標準ホモトピーを一つの三角形にし、もう一方を零として対角に沿って貼る。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：N7c の ∞ 引き戻し性の充填の対象。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：cospan の二射の差を二項直和からの chain map にする。
方針：第一成分 g、第二成分 −h の直和からの射を使う。
規約：HTT §1.2.13、N7.1。使われ方：標準引き戻しの fiber の入力。 -/
def fiberDifference (g : B ⟶ D) (h : C ⟶ D) : B ⊞ C ⟶ D := biprod.desc g (-h)

/-- 概要：二つの射の標準引き戻し候補は、差の射の mapping cone の −1 シフト。
方針：標準 fiber を二項直和からの差の射に適用する。
規約：HTT §1.2.13、N7.1。使われ方：標準引き戻し錐の頂点。 -/
abbrev pullbackFiber (g : B ⟶ D) (h : C ⟶ D) : Complex A := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber (fiberDifference g h)

/-- 概要：標準 fiber の B への脚。
方針：fiber の射影を二項直和の第一射影と合成する。
規約：HTT §1.2.13。使われ方：標準引き戻し錐の第一の辺。 -/
def pullbackProjectionB (g : B ⟶ D) (h : C ⟶ D) : pullbackFiber g h ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection (fiberDifference g h) ≫ biprod.fst

/-- 概要：標準 fiber の C への脚。
方針：fiber の射影を二項直和の第二射影と合成する。
規約：HTT §1.2.13。使われ方：標準引き戻し錐の第二の辺。 -/
def pullbackProjectionC (g : B ⟶ D) (h : C ⟶ D) : pullbackFiber g h ⟶ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection (fiberDifference g h) ≫ biprod.snd

/-- 概要：標準四角形の対角は C を通る厳密な合成。
方針：C への脚と h を合成する。
規約：HTT §1.2.13。使われ方：共通の対角辺に沿った二三角形の貼合せ。 -/
def pullbackDiagonal (g : B ⟶ D) (h : C ⟶ D) : pullbackFiber g h ⟶ D :=
  pullbackProjectionC g h ≫ h

/-- 概要：標準 fiber のホモトピーは二つの脚の合成の差の原始元。
方針：差の射への標準ホモトピーの微分を直和の二つの成分へ展開する。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：B を通る三角形の方程式。 -/
lemma pullbackHomotopy_differential (g : B ⟶ D) (h : C ⟶ D) :
    δ (-1) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (fiberDifference g h)) =
      Cochain.ofHom (pullbackProjectionB g h ≫ g) - Cochain.ofHom (pullbackDiagonal g h) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy_differential]
  simp only [fiberDifference, pullbackProjectionB, pullbackDiagonal, pullbackProjectionC,
    biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg, ← Category.assoc,
    Cochain.ofHom_add, Cochain.ofHom_neg, sub_eq_add_neg]

/-- 概要：標準四角形の B を通る三角形は mapping cone の標準ホモトピーを持つ。
方針：差の原始元を三つの chain map の合成構造にする。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：標準四角形の下側の二単体。 -/
def fiberLowerTriangle (g : B ⟶ D) (h : C ⟶ D) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pullbackProjectionB g h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pullbackDiagonal g h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy (fiberDifference g h))
    (pullbackHomotopy_differential g h)

/-- 概要：標準四角形の C を通る三角形は零ホモトピーを持つ。
方針：対角が C を通る厳密な合成であることを使う。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：標準四角形の上側の二単体。 -/
def fiberUpperTriangle (g : B ⟶ D) (h : C ⟶ D) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pullbackProjectionC g h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pullbackDiagonal g h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct _ _ _ 0 (by simp only [δ_zero, pullbackDiagonal, sub_self])

/-- 概要：標準 fiber の二つの三角形は共通の対角を持つ四角形へ貼り合わさる。
方針：Core の正方形の pushout に二単体を与える。
規約：HTT §1.2.13。使われ方：引き戻し性を検証する標準四角形。 -/
def standardFiberSquare (g : B ⟶ D) (h : C ⟶ D) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (fiberUpperTriangle g h).simplex)
    (SSet.yonedaEquiv.symm (fiberLowerTriangle g h).simplex) (by
      rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        (fiberUpperTriangle g h).d₁, (fiberLowerTriangle g h).d₁])

/-- 概要：標準四角形の上側三角形は指定した C を通る三角形。
方針：正方形の pushout の第一の包含での降下の式を使う。
規約：HTT §1.2.13。使われ方：標準四角形の辺と錐の計算。 -/
lemma standardFiberSquare_upper (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ standardFiberSquare g h =
      SSet.yonedaEquiv.symm (fiberUpperTriangle g h).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 概要：標準四角形の下側三角形は指定した B を通る三角形。
方針：正方形の pushout の第二の包含での降下の式を使う。
規約：HTT §1.2.13。使われ方：標準四角形の辺と錐の計算。 -/
lemma standardFiberSquare_lower (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ standardFiberSquare g h =
      SSet.yonedaEquiv.symm (fiberLowerTriangle g h).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 概要：標準四角形の右辺は元の射 g の辺。
方針：B を通る三角形の最後の辺で評価する。
規約：HTT §1.2.13。使われ方：固定 cospan の確認。 -/
lemma standardFiberSquare_right (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ standardFiberSquare g h = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge g).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, standardFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (fiberLowerTriangle g h).d₀]

/-- 概要：標準四角形の上辺は元の射 h の辺。
方針：C を通る三角形の最後の辺で評価する。
規約：HTT §1.2.13。使われ方：固定 cospan の確認。 -/
lemma standardFiberSquare_top (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ standardFiberSquare g h = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge h).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, standardFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (fiberUpperTriangle g h).d₀]

/-- 概要：標準 fiber の四角形を Core の JoinCone として読む。
方針：Core の正方形と cospan の join 錐の比較を使う。
規約：HTT Definition 1.2.13.4。使われ方：N7c の slice で終対象性を証明する対象。
ここでは錐の構成のみを行い、極限性はまだ主張しない。 -/
def standardFiberCone (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (standardFiberSquare g h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (standardFiberSquare g h)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
