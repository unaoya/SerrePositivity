module
public import SerrePositivity.KST.SConstruction.SPathRealization

/-! # S の経路実現から元の実現への面写像
概要：追加した先頭頂点を忘れる面を、単体的な自然変換と対角の写像にする。
方針：後続頂点の包含の自然性を先頭追加関手について計算する。
規約：射影の fiber 比較は別に証明する。使われ方：delooping の経路の境界射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：追加した先頭を除く後続頂点の包含。
方針：標準面 δ₀ を使う。
規約：全ての元の頂点を一つずらす。使われ方：経路構成の境界射。 -/
def simplicialPathTail (d : SimplexCategory) : d ⟶ SimplexPrefix.functor.obj d :=
  SimplexCategory.δ (0 : Fin (d.len + 2))

/-- 概要：後続頂点の包含は先頭追加した単体作用素について自然。
方針：各元の頂点の像が両側で一つずつずれることを比較する。
規約：厳密等号。使われ方：経路構成の境界の自然性。 -/
lemma simplicialPathTail_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    simplicialPathTail d ≫ SimplexPrefix.functor.map f = f ≫ simplicialPathTail e := by
  ext j : 3
  change Fin.cases 0 (fun i => (f.toOrderHom i).succ) ((0 : Fin (d.len + 2)).succAbove j) =
    (0 : Fin (e.len + 2)).succAbove (f.toOrderHom j)
  rw [Fin.succAbove_zero_apply, Fin.succAbove_zero_apply]
  rfl

/-- 概要：単体的経路構成から元の単体的対象への境界射。
方針：各次数で追加した先頭頂点を忘れる。
規約：任意の値の圏に適用。使われ方：S の経路の境界射の単体的モデル。 -/
def simplicialPathBoundary {C : Type u} [Category.{v} C] (X : SimplicialObject C) :
    simplicialPath X ⟶ X where
  app d := X.map (simplicialPathTail d.unop).op
  naturality {d e} f := by
    change X.map (SimplexPrefix.functor.map f.unop).op ≫ X.map (simplicialPathTail e.unop).op =
      X.map (simplicialPathTail d.unop).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp, ← op_comp]
    have h := simplicialPathTail_naturality f.unop
    exact congrArg (fun k => X.map k.op) h

/-- 概要：単体的経路構成の対角から元の対角への境界射。
方針：先頭を忘れる自然変換に対角関手を適用する。
規約：充填性の追加仮定なし。使われ方：経路実現の homotopy fiber の比較対象。 -/
def simplicialPathDiagonalBoundary (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialPath X) ⟶ simplicialDiagonalFunctor.obj X :=
  simplicialDiagonalFunctor.map (simplicialPathBoundary X)

/-- 概要：S の弱可縮な経路実現から元の core S の対角実現への境界射。
方針：単体的 core S に一般の境界射を適用する。
規約：fiber と loop の同値性はこの定義では主張しない。使われ方：delooping の境界写像。 -/
def sPathRealizationBoundary (C : SSet.{u}) : sPathRealization C ⟶ diagonalCoreSConstruction C :=
  simplicialPathDiagonalBoundary (simplicialCoreSConstruction C)

end SerrePositivity.KST.SConstruction
