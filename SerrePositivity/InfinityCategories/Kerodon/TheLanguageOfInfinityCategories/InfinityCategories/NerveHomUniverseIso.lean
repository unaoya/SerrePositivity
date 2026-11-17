module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：同じ宇宙内でHomだけを持ち上げた圏のnerveを元のnerveへ戻す。
方針：同じ全射列に元のULiftHomのup・downを適用する。
規約：元の対象・全射・全単体作用素を保ち、単体に外側のULiftを追加しない。
使われ方：全要素圏のGrothendieck係数を元の全要素nerveへ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open CategoryTheory
variable (C : Type u) [Category.{v} C]

/-- Homの宇宙だけを持ち上げた元のnerveの、同じ全射列の実同型。 -/
def nerveHomUniverseIso : nerve (ULiftHom.{max u v} C) ≅ nerve C where
  hom :=
    { app _ := ↾fun σ => σ ⋙ ULiftHom.down.{v,u,max u v}
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun σ => σ ⋙ ULiftHom.up.{v,u,max u v}
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 同じ全射列の同型は、元の圏の関手にも自然。 -/
theorem nerveHomUniverseIso_naturality {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    nerveMap (ULiftHom.down.{v,u,max u v} ⋙ F ⋙ ULiftHom.up) ≫
      (nerveHomUniverseIso D).hom = (nerveHomUniverseIso C).hom ≫ nerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl
end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
