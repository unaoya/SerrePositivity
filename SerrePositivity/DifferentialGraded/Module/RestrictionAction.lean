module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.Representable
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 制限加群と代表加群の作用の成分式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

lemma restrictModule_action (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (M : RightModule A E)
    {x y : Dᵒᵖ} {p i n : ℤ} (f : GradedHom A x y p) (v : (M.obj (F.obj x)).X i)
    (hn : i + p = n) :
    moduleAction A (restrictModule A D E F M) f v hn =
      moduleAction A M ((F.map x y).f p f) v hn := rfl

omit [DGCategory A E] in
lemma representable_action (z : D) {x y : Dᵒᵖ} {p i n : ℤ}
    (f : GradedHom A x y p) (v : GradedHom A x.unop z i) (hn : i + p = n) :
    moduleAction A (representable A z) f v hn =
      forward A (x := y.unop) (y := x.unop) (z := z) f v (by omega) := rfl

omit [DGCategory A E] in
lemma moduleAction_units_smul (M : RightModule A D) {x y : Dᵒᵖ} {p i n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X i) (hn : i + p = n) (a : ℤˣ) :
    moduleAction A M f (a • v) hn = a • moduleAction A M f v hn := by
  simp only [moduleAction, Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded
