module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison

/-!
概要：同じ thickening 対象で、実対象の指定同定から二つの自己 Hom を同定する。
方針：端点の等しい path の一意性と、元の豊穣恒等の保存を使う。
規約：対象の同定を保持。使われ方：二つの実 prism の初点の自己 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の線形順序の thickening で、元の自己 path の豊穣恒等は全射。 -/
lemma thickeningSelf_eId_epi {J : Type u} [LinearOrder J] (o : SimplicialThickening J) :
    Epi (eId SSet o) := by
  haveI : Subsingleton (Path o.as o.as) := ⟨fun p q ↦ by
    rw [thickeningPath_end_eq_id o.as p, thickeningPath_end_eq_id o.as q]⟩
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [epi_iff_surjective]
  intro F
  refine ⟨PUnit.unit, ?_⟩
  apply CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)

/-- 同じ対象の表示変更は、元の豊穣恒等を同じ向きに移す。 -/
lemma simplicialHom_id_display {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B : C} (h : A = B) :
    eId SSet A ≫ eqToHom (congrArg₂ SimplicialCategory.sHom h h) = eId SSet B := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ元の対象同定は、二つの豊穣関手の自己 Hom の作用を一致させる。 -/
lemma thickeningSelfHom_comparison {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (R S : EnrichedFunctor SSet (SimplicialThickening J) C)
    (o : SimplicialThickening J) (h : R.obj o = S.obj o) :
    R.map o o ≫ eqToHom (congrArg₂ SimplicialCategory.sHom h h) = S.map o o := by
  haveI := thickeningSelf_eId_epi o
  apply (cancel_epi (eId SSet o)).mp
  rw [← Category.assoc, R.map_id, S.map_id]
  exact simplicialHom_id_display h

end SerrePositivity.InfinityCategories.F2
