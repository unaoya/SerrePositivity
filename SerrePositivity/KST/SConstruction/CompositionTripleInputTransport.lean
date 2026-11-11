module
public import SerrePositivity.KST.SConstruction.CompositionTripleTetrahedronLifting

/-! # 次の結合替えの入力表示を合わせても元の全面を保持する
概要：前の実持ち上げの出力面に合わせ、次の元の全基底四面体の入力表示だけを移す。
方針：入力した実合成面の厳密な等号を消去し、同じ全三単体と残面を保持する。
規約：全基底四面体と残る実出力面を変更しない。
使われ方：六つの結合替えを独立な選択にせず、全共有面に沿って逐次持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
variable {E : SSet.{u}} {w x y z : E _⦋0⦌}
  {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
  {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
  (first : SSet.Edge.CompStruct a b ab) (second : SSet.Edge.CompStruct b c bc)

/-- 右結合入力の表示を合わせても、元の全四面体と同じ左結合出力を厳密に保持する。 -/
def compositionTripleInputTransport
    {right right' : SSet.Edge.CompStruct a bc abc} (h : right = right')
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron first second right) :
    {V : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleTetrahedron first second right' //
      V.simplex = R.simplex ∧ V.left = R.left} := by
  cases h
  exact ⟨R, rfl, rfl⟩

/-- 左結合入力の表示を合わせても、元の全四面体と同じ右結合出力を厳密に保持する。 -/
def compositionTripleRightInputTransport
    {left left' : SSet.Edge.CompStruct ab c abc} (h : left = left')
    (R : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left) :
    {V : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionTripleRightTetrahedron first second left' //
      V.simplex = R.simplex ∧ V.right = R.right} := by
  cases h
  exact ⟨R, rfl, rfl⟩

end SerrePositivity.KST.SConstruction
