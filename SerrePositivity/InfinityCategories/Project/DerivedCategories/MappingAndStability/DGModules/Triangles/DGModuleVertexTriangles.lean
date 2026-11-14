module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleVertexProperty
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PretriangulatedInstance

/-! # 実加群 cofiber 三角形の対象条件

概要：K(D) の三角的対象条件は通常の h の distinguished triangle の第三項で閉じる。
方針：実 cofiber 表示の指定辺から標準 cone へ比較する。
規約：三角関手性そのものはまだ主張しない。使われ方：実安定閉包の生成条件の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 任意の端点表示の実 cofiber も K(D) の三角的対象条件を保つ。 -/
lemma dgModuleHoProperty_cofiber_any {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e)
    (hx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P (SSet.HomotopyCategory.mk x))
    (hy : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P (SSet.HomotopyCategory.mk y)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P (SSet.HomotopyCategory.mk s.cofiber) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty_cofiber A D P s hx hy

/-- 通常の h の実 cofiber 三角形の第三項で閉じる。 -/
instance dgModuleHoProperty_isTriangulatedClosed₃ :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P).IsTriangulatedClosed₃ := .mk' (by
  intro T hT h₁ h₂
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have ha := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hb := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P).prop_of_iso (Triangle.π₂.mapIso e) h₂
  let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow t.square) := {
    toZeroTriangle := t
    bottom_edge := by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge]
      exact (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D P).prop_of_iso (Triangle.π₃.mapIso e.symm)
    (dgModuleHoProperty_cofiber_any A D P s ha hb))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
