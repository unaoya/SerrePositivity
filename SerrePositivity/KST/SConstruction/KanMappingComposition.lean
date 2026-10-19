module
public import SerrePositivity.KST.SConstruction.KanMappingSpanComposition

/-! # 元の二辺と実三角形を保持する合成
概要：端点の合う元の二辺から、元の二辺を両面に持つ実合成三角形を構成する。
方針：辺の合成類を代表し、証明済みの合成構造の判定から全三辺の実二単体を得る。
規約：結論を成分の等式で終えず、合成辺と全三角形を保持する。
使われ方：実補正有限列を、全合成証人を記録した一本の比較辺へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の二辺を二面として保持する、実合成辺と全三角形。 -/
structure KanMappingComposition {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) where
  /-- 元の二辺の実合成辺。 -/
  edge : E.Edge x z
  /-- 元の二辺と合成辺の全二単体。 -/
  triangle : SSet.Edge.CompStruct a b edge

/-- 二辺の合成を、全三辺と実二単体を伴って構成する。 -/
def kanMappingComposition {E : SSet.{u}} [Quasicategory E] {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) : KanMappingComposition a b := by
  let hex := homotopyCategory_homMk_surjective x z
    (SSet.Truncated.HomotopyCategory.homMk a.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk b.toTruncated)
  let e := SSet.Edge.ofTruncated hex.choose
  exact ⟨e, SSet.Edge.CompStruct.ofTruncated
    (compStruct_nonempty_of_homMk_fac hex.choose_spec.symm).some⟩

end SerrePositivity.KST.SConstruction
