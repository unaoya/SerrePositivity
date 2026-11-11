module
public import SerrePositivity.KST.SConstruction.KZeroToTriangulatedMap
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FundamentalNerveHomotopy

/-! # 可換群の一対象圏における loop の自然性
概要：自然変換の両端補正は閉じた辺の評価では相殺する。
方針：自然性の式を加法群へ戻して同じ成分を消去する。
規約：異なる頂点の成分を同一視しない。
使われ方：実際の K₀ 比較の対象類の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 可換群の一対象圏への自然変換は、閉じた射の群値を保つ。 -/
lemma singleObj_loop_naturality {C : Type v} [Category.{u} C]
    {A : Type u} [AddCommGroup A]
    {F G : C ⥤ AsSmall.{u} (SingleObj (Multiplicative A))}
    (α : F ⟶ G) {x : C} (f : x ⟶ x) :
    (F.map f).down.toAdd = (G.map f).down.toAdd := by
  have h := congrArg (fun g ↦ g.down.toAdd) (α.naturality f)
  change (α.app x).down.toAdd + (F.map f).down.toAdd =
    (G.map f).down.toAdd + (α.app x).down.toAdd at h
  rw [add_comm (G.map f).down.toAdd] at h
  exact add_left_cancel h

/-- 一対象圏への辺の評価は、端点表示を変えても同じ一次単体なら一致する。 -/
lemma singleObj_edge_value_congr {B : SSet.{u}} {A : Type u} [AddCommGroup A]
    (F : hoFunctor.obj B ⥤ AsSmall.{u} (SingleObj (Multiplicative A)))
    {x y x' y' : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) x y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj B) x' y')
    (h : e.edge = f.edge) :
    (F.map (SSet.Truncated.HomotopyCategory.homMk e)).down.toAdd =
      (F.map (SSet.Truncated.HomotopyCategory.homMk f)).down.toAdd := by
  have hx : x = x' := e.src_eq.symm.trans ((congrArg (B.δ 1) h).trans f.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans ((congrArg (B.δ 0) h).trans f.tgt_eq)
  cases hx
  cases hy
  have he : e = f := SSet.Truncated.Edge.ext h
  rw [he]

end SerrePositivity.KST.SConstruction
