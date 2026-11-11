module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex

/-!
概要：有限極限から反対圏の同じ有限図式の余極限を構成する。
方針：非退化単体の反転同値と、元の図式を回収する二重反転を使う。
規約：元の圏の有限余極限は結論しない。使われ方：一般安定性判定の双対化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ有限図式と極限錐を反転して普遍余錐を得る。 -/
lemma oppositeDiagram_double_return {K X : SSet.{u}} (p : K ⟶ X.op) :
    (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map p ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom) = p := by
  rw [Functor.map_comp]
  have he : SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app X).hom =
      (SSet.opFunctorCompOpFunctorIso.app X.op).hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he]
  change _ ≫ (SSet.opFunctor ⋙ SSet.opFunctor).map p ≫
    (SSet.opFunctorCompOpFunctorIso.app X.op).hom = _
  calc
    _ = (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
        ((SSet.opFunctorCompOpFunctorIso.app K).hom ≫ p) :=
      congrArg (fun f ↦ (SSet.opFunctorCompOpFunctorIso.app K).inv ≫ f)
        (SSet.opFunctorCompOpFunctorIso.hom.naturality p)
    _ = p := Iso.inv_hom_id_assoc _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
