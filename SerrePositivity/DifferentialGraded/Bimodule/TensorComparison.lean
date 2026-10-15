module
public import SerrePositivity.DifferentialGraded.Bimodule.Uncurry
public import SerrePositivity.DifferentialGraded.Bimodule.Ext

/-! # bimoduleとtensor積dg圏上の関手の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

namespace BimoduleTensorFunctor
lemma toBimodule_rightAt (F : BimoduleTensorFunctor A B C) (c : C) :
    F.toBimodule.rightAt c = F.rightAt c := rfl

lemma toBimodule_leftAt (F : BimoduleTensorFunctor A B C) (b : B) :
    F.toBimodule.leftAt b = F.leftAt b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := F.toBimodule.leftAt b) (G := F.leftAt b) (fun _ => rfl)
  intro c d
  change (F.toBimodule.toFunctor.map c d ≫
    moduleHomπ A B (F.rightAt c) (F.rightAt d) b) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact F.toBimodule_map_π c d b

omit [Small.{u} B] in
/-- 純粋tensorの像は制限された二作用の豊穣順合成。 -/
lemma map_tensorElement (F : BimoduleTensorFunctor A B C)
    {x y : DGTensorCategory A Bᵒᵖ C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    (F.map x y).f n (dgTensorElement A f g hn) =
      (p * q).negOnePow • (((F.rightAt x.2).map x.1 y.1).f p f).comp
        (((F.leftAt y.1.unop).map x.2 y.2).f q g) hn := by
  have h := DGFunctor.map_forward_cochain A F (x := x) (y := (y.1, x.2)) (z := y)
    ((dgTensorFirstHom A Bᵒᵖ C x.2 x.1 y.1).f p f)
    ((dgTensorSecondHom A Bᵒᵖ C y.1 x.2 y.2).f q g) hn
  rw [dgTensor_first_then_second] at h
  exact h
end BimoduleTensorFunctor

namespace Bimodule
lemma toTensorFunctor_toBimodule (M : Bimodule A B C) :
    M.toTensorFunctor.toBimodule = M := by
  apply ext_rightAt_leftAt
  · intro c
    exact (M.toTensorFunctor.toBimodule_rightAt c).trans (M.toTensorFunctor_rightAt c)
  · intro b
    exact (M.toTensorFunctor.toBimodule_leftAt b).trans (M.toTensorFunctor_leftAt b)
end Bimodule

namespace BimoduleTensorFunctor
lemma toBimodule_toTensorFunctor (F : BimoduleTensorFunctor A B C) :
    F.toBimodule.toTensorFunctor = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := F.toBimodule.toTensorFunctor) (G := F) (fun _ => rfl)
  intro x y
  change F.toBimodule.uncurryHom x y ≫ 𝟙 _ = F.map x y
  rw [Category.comp_id]
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (F.toBimodule.uncurryHom x y).f n (dgTensorElement A f g hn) =
    (F.map x y).f n (dgTensorElement A f g hn)
  have hl := congrArg (fun t => t.f q g) (F.toBimodule_map_π x.2 y.2 y.1.unop)
  change F.toBimodule.leftCochain g y.1.unop = ((F.leftAt y.1.unop).map x.2 y.2).f q g at hl
  have he := congrArg (fun t : Cochain (F.obj (y.1, x.2)) (F.obj y) q =>
    (p * q).negOnePow • (((F.rightAt x.2).map x.1 y.1).f p f).comp t hn) hl
  exact (F.toBimodule.uncurryHom_apply f g hn).trans
    (he.trans (F.map_tensorElement f g hn).symm)
end BimoduleTensorFunctor

variable (A B C)
/-- curried全Hom end表示とtensor積dg圏上の豊穣関手表示の対象データの同値。 -/
def bimoduleEquivTensorFunctor : Bimodule A B C ≃ BimoduleTensorFunctor A B C where
  toFun := Bimodule.toTensorFunctor
  invFun := BimoduleTensorFunctor.toBimodule
  left_inv := Bimodule.toTensorFunctor_toBimodule
  right_inv := BimoduleTensorFunctor.toBimodule_toTensorFunctor

end SerrePositivity.DifferentialGraded
