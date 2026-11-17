module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine

/-!
概要：Arrow の実際の射は、同じ nerve のタプル被覆の逆像を保つ。
方針：有限交叉と逆像の交換、既存の mapCechNerve の射影の公式を使う。
規約：閉中心に独立な被覆を選ばず、元の被覆の逆像を保持する。
使われ方：二つの実際の係数関手の閉中心への引き戻しを照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Arrow の射による元の被覆の逆像と、同じタプル開の逆像は一致する。 -/
theorem schemeCechTupleOpen_mapCechNerve_preimage {f g : Arrow Scheme.{u}}
    (F : f ⟶ g) {ι : Type} (U : ι → g.left.Opens)
    (n : SimplexCategoryᵒᵖ) (t : Fin (n.unop.len + 1) → ι) :
    schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) n t =
      (Arrow.mapCechNerve F).app n ⁻¹ᵁ schemeCechTupleOpen g.hom U n t := by
  rw [schemeCechTupleOpen, schemeCechTupleOpen, schemePreimage_finite_iInf]
  congr 1
  funext j
  have he : (Arrow.mapCechNerve F).app n ≫
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g.hom) j =
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f.hom) j ≫ F.left := by
    rw [Arrow.mapCechNerve_app]
    exact WidePullback.lift_π _ _ _ _ j
  change (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f.hom) j ≫ F.left) ⁻¹ᵁ U (t j) =
    ((Arrow.mapCechNerve F).app n ≫
      WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g.hom) j) ⁻¹ᵁ U (t j)
  exact congrArg (fun k : f.cechNerve.obj n ⟶ g.left ↦ k ⁻¹ᵁ U (t j)) he.symm

end SerrePositivity.AlgebraicGeometry
