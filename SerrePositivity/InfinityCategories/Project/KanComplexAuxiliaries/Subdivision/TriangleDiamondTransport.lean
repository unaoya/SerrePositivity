module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SimplicialEqualityTransport

/-! # 四辺と共通対角辺を保つ同じ二つの実二単体の移送
概要：元の二つの二単体全体を同じ単体集合へ移し、全四辺と共通対角辺を厳密に回収する。
方針：単体集合の表示等号で同じ二単体を写し、四面の依存等号と共通面の等号を移す。
規約：新しい二単体を充填・選択しない。元の全二単体の像を証拠として保存する。
使われ方：三入力 BF 比較の四辺の照合を同じ実二次元比較データへ束ねる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 全四辺と同じ対角辺を保持する、同じ単体集合内の二つの実二単体。 -/
structure TriangleDiamondData (E : SSet.{u})
    (firstLower secondLower firstUpper secondUpper : E _⦋1⦌) where
  /-- 第一経路の全二単体。 -/
  first : E _⦋2⦌
  /-- 第二経路の全二単体。 -/
  second : E _⦋2⦌
  /-- 第一経路の元の下辺。 -/
  first_lower : E.δ 2 first = firstLower
  /-- 第二経路の元の下辺。 -/
  second_lower : E.δ 2 second = secondLower
  /-- 第一経路の元の上辺。 -/
  first_upper : E.δ 0 first = firstUpper
  /-- 第二経路の元の上辺。 -/
  second_upper : E.δ 0 second = secondUpper
  /-- 全二単体が共有する同じ実対角辺。 -/
  diagonal : E.δ 1 first = E.δ 1 second

/-- 元の二単体の全像を証拠として保存し、全四辺と共通対角辺を同時に回収する。 -/
def triangleDiamondTransportData {E D : SSet.{u}} (e : E = D) (s t : E _⦋2⦌)
    (firstLower secondLower firstUpper secondUpper : D _⦋1⦌)
    (hfl : HEq (E.δ 2 s) firstLower) (hsl : HEq (E.δ 2 t) secondLower)
    (hfu : HEq (E.δ 0 s) firstUpper) (hsu : HEq (E.δ 0 t) secondUpper)
    (hd : E.δ 1 s = E.δ 1 t) :
    {T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData D firstLower secondLower firstUpper secondUpper //
      T.first = (eqToHom e).app (Opposite.op ⦋2⦌) s ∧
      T.second = (eqToHom e).app (Opposite.op ⦋2⦌) t} :=
  ⟨{ first := (eqToHom e).app (Opposite.op ⦋2⦌) s
     second := (eqToHom e).app (Opposite.op ⦋2⦌) t
     first_lower := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face_of_heq e 2 s firstLower hfl
     second_lower := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face_of_heq e 2 t secondLower hsl
     first_upper := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face_of_heq e 0 s firstUpper hfu
     second_upper := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_face_of_heq e 0 t secondUpper hsu
     diagonal := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialEqualityTransport_common_face e 1 s t hd }, rfl, rfl⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
