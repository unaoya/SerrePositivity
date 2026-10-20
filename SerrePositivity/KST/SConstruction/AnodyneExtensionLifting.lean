module
public import SerrePositivity.KST.SConstruction.AnodyneExtensionSpecifiedVertices
public import SerrePositivity.KST.SConstruction.AnodyneRelativeFibrationFamily

/-! # 指定された全基底延長を保つ anodyne 選択頂点の持ち上げ
概要：fibration に沿い元の全指定部分と全基底延長を保つ実延長を選択空間へ回収する。
方針：同じ可換四角形の実持ち上げを、そのまま既存の指定頂点へ入れる。
規約：基底の全写像と指定部分を厳密に保持し、代表を選び直さない。
使われ方：終辺消去の全基底四面体を、元の六結合替えの残面に合わせて持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 元の全指定部分と指定全基底延長を保つ、同じ実延長の選択頂点。 -/
def anodyneExtensionLiftVertex {A D E B : SSet.{u}}
    (i : A ⟶ D) (hi : anodyneExtensions i) (p : E ⟶ B) [Fibration p]
    (h : A ⟶ E) (b : D ⟶ B) (hb : h ≫ p = i ≫ b) :
    {v : (anodyneExtensionChoices i h) _⦋0⦌ // anodyneExtensionAt i h v ≫ p = b} := by
  let : HasLiftingProperty i p :=
    hi p ((HomotopicalAlgebra.fibration_iff p).mp inferInstance)
  let sq : CommSq h i p b := ⟨hb⟩
  let v := anodyneExtensionVertex i h sq.lift sq.fac_left
  exact ⟨v, by rw [anodyneExtensionAt_vertex]; exact sq.fac_right⟩

end SerrePositivity.KST.SConstruction
