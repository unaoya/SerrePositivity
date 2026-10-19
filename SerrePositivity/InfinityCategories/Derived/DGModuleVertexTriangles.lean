module
public import SerrePositivity.InfinityCategories.Derived.DGModuleVertexProperty
public import SerrePositivity.InfinityCategories.Stable.PretriangulatedInstance

/-! # 実加群 cofiber 三角形の対象条件

概要：K(D) の三角的対象条件は通常の h の distinguished triangle の第三項で閉じる。
方針：実 cofiber 表示の指定辺から標準 cone へ比較する。
規約：三角関手性そのものはまだ主張しない。使われ方：実安定閉包の生成条件の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 任意の端点表示の実 cofiber も K(D) の三角的対象条件を保つ。 -/
lemma dgModuleHoProperty_cofiber_any {x y : (dgModuleNerve A D) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D)) x y}
    (s : CofiberSquare e)
    (hx : dgModuleHoProperty A D P (SSet.HomotopyCategory.mk x))
    (hy : dgModuleHoProperty A D P (SSet.HomotopyCategory.mk y)) :
    dgModuleHoProperty A D P (SSet.HomotopyCategory.mk s.cofiber) := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  exact dgModuleHoProperty_cofiber A D P s hx hy

/-- 通常の h の実 cofiber 三角形の第三項で閉じる。 -/
instance dgModuleHoProperty_isTriangulatedClosed₃ :
    (dgModuleHoProperty A D P).IsTriangulatedClosed₃ := .mk' (by
  intro T hT h₁ h₂
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have ha := (dgModuleHoProperty A D P).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hb := (dgModuleHoProperty A D P).prop_of_iso (Triangle.π₂.mapIso e) h₂
  let s : CofiberSquare (squareBottomArrow t.square) := {
    toZeroTriangle := t
    bottom_edge := by
      rw [squareBottomArrow_edge]
      exact (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  exact (dgModuleHoProperty A D P).prop_of_iso (Triangle.π₃.mapIso e.symm)
    (dgModuleHoProperty_cofiber_any A D P s ha hb))

end SerrePositivity.InfinityCategories
