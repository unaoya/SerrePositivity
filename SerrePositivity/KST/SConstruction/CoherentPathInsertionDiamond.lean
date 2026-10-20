module
public import SerrePositivity.KST.SConstruction.CoherentPathInsertion
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # 二つの切断点の挿入から得る同じ Path の実二三角形
概要：元の Path に二点を加える二経路を、共通対角辺を持つ実二単体で結ぶ。
方針：元の包含射二つの列を nerve の二単体として構成し、同じ豊穣作用で写す。
規約：Kan 充填や辺の再選択を使わず、同じ全二単体を保持する。
使われ方：三入力の四面体の全豊穣作用から合成比較の実二次元データを取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
variable {J : Type u} [LinearOrder J] {a b c d : J}

/-- Path の包含の元の可換三角形を、その同じ二射列の実二単体にする。 -/
def coherentPathInclusionTriangle {p q r : Path a c} (i : p ⟶ q) (j : q ⟶ r) (k : p ⟶ r) :
    SSet.Edge.CompStruct (nerve.edgeMk i) (nerve.edgeMk j) (nerve.edgeMk k) := by
  have hk : i ≫ j = k := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _
  refine SSet.Edge.CompStruct.mk (ComposableArrows.mk₂ i j)
    (nerve.δ₂_mk₂_eq i j) (nerve.δ₀_mk₂_eq i j) ?_
  exact (nerve.δ₁_mk₂_eq i j).trans (congrArg ComposableArrows.mk₁ hk)

/-- 第一切断点の挿入後に第二切断点を挿入した共通の Path。 -/
def coherentDoubleInsertedPath (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c)
    (p : Path a c) : Path a c :=
  coherentPathInsert had hdc (coherentPathInsert hab hbc p)

/-- 第二切断点を先に加えた Path から共通 Path への元の包含。 -/
def coherentDoubleInsertSecondInclusion
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :
    coherentPathInsert had hdc p ⟶ coherentDoubleInsertedPath hab hbc had hdc p := by
  refine ⟨⟨⟨?_⟩⟩⟩
  intro x hx
  exact hx.elim (fun h => Or.inl (Or.inl h)) Or.inr

/-- 元の Path から共通 Path への同じ対角包含。 -/
def coherentDoubleInsertDiagonal
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :
    p ⟶ coherentDoubleInsertedPath hab hbc had hdc p :=
  (coherentPathInsertTransformation hab hbc).app p ≫
    (coherentPathInsertTransformation had hdc).app (coherentPathInsert hab hbc p)

/-- 第一切断点を先に加える経路の元の二単体。 -/
def coherentDoubleInsertFirstTriangle
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :=
  coherentPathInclusionTriangle ((coherentPathInsertTransformation hab hbc).app p)
    ((coherentPathInsertTransformation had hdc).app (coherentPathInsert hab hbc p))
    (coherentDoubleInsertDiagonal hab hbc had hdc p)

/-- 第二切断点を先に加える経路の元の二単体。同じ対角包含を保つ。 -/
def coherentDoubleInsertSecondTriangle
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :=
  coherentPathInclusionTriangle ((coherentPathInsertTransformation had hdc).app p)
    (coherentDoubleInsertSecondInclusion hab hbc had hdc p)
    (coherentDoubleInsertDiagonal hab hbc had hdc p)

/-- 第一経路の全二単体は、元の二包含射の列そのもの。 -/
lemma coherentDoubleInsertFirstTriangle_simplex
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :
    (coherentDoubleInsertFirstTriangle hab hbc had hdc p).simplex =
      ComposableArrows.mk₂ ((coherentPathInsertTransformation hab hbc).app p)
        ((coherentPathInsertTransformation had hdc).app (coherentPathInsert hab hbc p)) := rfl

/-- 第二経路も、同じ共通 Path に終わる元の二包含射の列そのもの。 -/
lemma coherentDoubleInsertSecondTriangle_simplex
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :
    (coherentDoubleInsertSecondTriangle hab hbc had hdc p).simplex =
      ComposableArrows.mk₂ ((coherentPathInsertTransformation had hdc).app p)
        (coherentDoubleInsertSecondInclusion hab hbc had hdc p) := rfl

/-- 同じ豊穣作用で写した第一経路の実二単体。 -/
def coherentDoubleInsertMappedFirstTriangle {E : SSet.{u}} (m : nerve (Path a c) ⟶ E)
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :=
  (coherentDoubleInsertFirstTriangle hab hbc had hdc p).map m

/-- 同じ豊穣作用で写した第二経路の実二単体。同じ対角辺の全写像を保持する。 -/
def coherentDoubleInsertMappedSecondTriangle {E : SSet.{u}} (m : nerve (Path a c) ⟶ E)
    (hab : a ≤ b) (hbc : b ≤ c) (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :=
  (coherentDoubleInsertSecondTriangle hab hbc had hdc p).map m

/-- 写した二つの全二単体も、同じ元の対角辺を厳密に共有する。 -/
lemma coherentDoubleInsertMappedTriangles_diagonal {E : SSet.{u}}
    (m : nerve (Path a c) ⟶ E) (hab : a ≤ b) (hbc : b ≤ c)
    (had : a ≤ d) (hdc : d ≤ c) (p : Path a c) :
    E.δ 1 (coherentDoubleInsertMappedFirstTriangle m hab hbc had hdc p).simplex =
      E.δ 1 (coherentDoubleInsertMappedSecondTriangle m hab hbc had hdc p).simplex :=
  (coherentDoubleInsertMappedFirstTriangle m hab hbc had hdc p).d₁.trans
    (coherentDoubleInsertMappedSecondTriangle m hab hbc had hdc p).d₁.symm

end SerrePositivity.KST.SConstruction
