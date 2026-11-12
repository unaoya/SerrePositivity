module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic

/-! # dg nerve の境界面の評価

概要：指定された境界から面と頂点を評価し、共通の先頭面での一致を記録する。
方針：標準単体の面の合成と境界包含の単射性で計算する。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：N7b の零対象の境界充填。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：境界に指定された単体的写像の各面の像。
方針：標準単体から境界への面包含を合成して米田対応で評価する。
規約：HTT §1.2.12。使われ方：既知面の単体データ。 -/
def face {X : SSet.{u}} {n : ℕ} (b : (SSet.boundary (n + 1) : SSet.{u}) ⟶ X)
    (i : Fin (n + 2)) : X _⦋n⦌ := SSet.yonedaEquiv (SSet.boundary.ι i ≫ b)

/-- 概要：面の一頂点を境界に含めると、対応する大域頂点の包含になる。
方針：境界包含を打ち消し、標準零単体の有限順序写像を比較する。
規約：HTT §1.2.12。使われ方：面の零終端の確認。 -/
lemma vertex_face {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ k) ≫ SSet.boundary.ι.{u} j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (j.succAbove k) := by
  apply (cancel_mono (SSet.boundary (n + 1)).ι).1
  rw [Category.assoc, SSet.boundary.ι_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.objEquiv.injective
  ext i : 3
  rfl

/-- 概要：境界の面の頂点の値は、同じ大域頂点の値。
方針：米田対応の自然性と頂点包含の合成の式を用いる。
規約：HTT §1.2.12。使われ方：固定した端点を全ての面へ移す。 -/
lemma face_vertex {X : SSet.{u}} {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u}) ⟶ X)
    (j : Fin (n + 2)) (k : Fin (n + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ k).op (face b j) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (j.succAbove k) ≫ b) := by
  rw [face, SSet.yonedaEquiv_naturality]
  rw [← Category.assoc, vertex_face]

/-- 概要：二つの境界面の共通の先頭面は一致する。
方針：境界包含を打ち消し、最終面と他の面の単体的恒等式を使う。
規約：HTT §1.2.12。使われ方：零終端の外延性に必要な先頭面の一致。 -/
lemma face_front {X : SSet.{u}} {n : ℕ}
    (b : (SSet.boundary (n + 2) : SSet.{u}) ⟶ X) (j : Fin (n + 2)) :
    X.δ (Fin.last (n + 1)) (face b j.castSucc) =
      X.δ j (face b (Fin.last (n + 2))) := by
  simp only [face, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (SSet.boundary (n + 2)).ι).1
  simp only [Category.assoc, SSet.boundary.ι_ι]
  simpa only [Fin.succ_last] using (SSet.stdSimplex.δ_comp_δ (Fin.le_last j)).symm

/-- 概要：二つの境界面の共通の後続面は一致する。
方針：境界包含を打ち消し、最初の面と他の面の単体的恒等式を使う。
規約：HTT §1.2.12 の双対。使われ方：零始域の外延性に必要な後続面の一致。 -/
lemma face_back {X : SSet.{u}} {n : ℕ}
    (b : (SSet.boundary (n + 2) : SSet.{u}) ⟶ X) (j : Fin (n + 2)) :
    X.δ 0 (face b j.succ) = X.δ j (face b 0) := by
  simp only [face, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (SSet.boundary (n + 2)).ι).1
  simp only [Category.assoc, SSet.boundary.ι_ι]
  exact SSet.stdSimplex.δ_comp_δ (Fin.zero_le j)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryEvaluation
