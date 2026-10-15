module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryComposition
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryRestriction

/-! # bimoduleの実際のuncurried dg関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 全Homで単位・合成を保存するtensor積dg圏上の関手。 -/
def toTensorFunctor (M : Bimodule A B C) : BimoduleTensorFunctor A B C where
  obj x := M.value x.1.unop x.2
  map := M.uncurryHom
  map_id := M.uncurryHom_identity
  map_comp := M.uncurryHom_comp

lemma toTensorFunctor_rightAt (M : Bimodule A B C) (c : C) :
    M.toTensorFunctor.rightAt c = M.rightAt c := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (M.toTensorFunctor.rightAt c).toFunctor) (G := (M.rightAt c).toFunctor) (fun _ => rfl)
  intro x y
  change (dgTensorFirstHom A Bᵒᵖ C c x y ≫ M.uncurryHom (x, c) (y, c)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact M.uncurryHom_first c x y

lemma toTensorFunctor_leftAt (M : Bimodule A B C) (b : B) :
    M.toTensorFunctor.leftAt b = M.leftAt b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := M.toTensorFunctor.leftAt b) (G := M.leftAt b) (fun _ => rfl)
  intro c d
  change (dgTensorSecondHom A Bᵒᵖ C (op b) c d ≫
    M.uncurryHom (op b, c) (op b, d)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact M.uncurryHom_second b c d

end SerrePositivity.DifferentialGraded.Bimodule
