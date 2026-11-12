module
public import SerrePositivity.DifferentialGraded.Functor.Closed
/-!
概要：二重反対 dg 圏を元の dg 圏へ戻す、全 Hom が恒等の実 dg 関手。
方針：二つの Koszul 交換を対称律で相殺する。
規約：全整数次数の合成を保持。使われ方：普遍余単位の comma の実二射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory BraidedCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
/-- 二重の反対 dg 圏から元の対象・全 Hom を回収する実 dg 関手。 -/
def dgDoubleOppositeDown : DGFunctor R Cᵒᵖᵒᵖ C where
  obj x := x.unop.unop
  map x y := 𝟙 (homObject R C x.unop.unop y.unop.unop)
  map_id x := by
    change eId (Complex R) x.unop.unop ≫ 𝟙 _ = _
    exact Category.comp_id _
  map_comp x y z := by
    change eComp (Complex R) x y z ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp (Complex R) x.unop.unop y.unop.unop z.unop.unop
    rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
    rw [eComp_op_eq (Complex R) z y x,
      eComp_op_eq (Complex R) x.unop y.unop z.unop,
      ← Category.assoc]
    change ((β_ (homObject R C x.unop.unop y.unop.unop)
      (homObject R C y.unop.unop z.unop.unop)).hom ≫
        (β_ (homObject R C y.unop.unop z.unop.unop)
          (homObject R C x.unop.unop y.unop.unop)).hom) ≫
      eComp (Complex R) x.unop.unop y.unop.unop z.unop.unop = _
    rw [SymmetricCategory.symmetry, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
