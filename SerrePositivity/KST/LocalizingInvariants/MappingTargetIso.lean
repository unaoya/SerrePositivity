module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveTargetMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor

/-!
概要：終点の同型は、元の関手が Hom に誘導する写像の全単射性を保つ。
方針：同型による後合成の二つの全単射を、関手の合成保存で比較する。
規約：任意の圏と関手。使われ方：cofiber の右随伴像と零始点矢印の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma functorMap_bijective_of_targetIso {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (x y z : C) (e : y ≅ z)
    (h : Function.Bijective (F.map (X := x) (Y := z))) :
    Function.Bijective (F.map (X := x) (Y := y)) := by
  constructor
  · intro f g hfg
    apply (cancel_mono e.hom).1
    apply h.injective
    simpa only [Functor.map_comp] using congrArg (fun t => t ≫ F.map e.hom) hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective (f ≫ F.map e.hom)
    refine ⟨g ≫ e.inv, ?_⟩
    rw [Functor.map_comp, hg, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- 頂点の実同型を、任意のパラメータ上の定値関手の実同型へ移す。 -/
def constantVertexIso (A : SSet.{u}) {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.const x : A ⟶ X) (SSet.const y) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A e.hom
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A e.inv
  hom_inv_id := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, e.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id]
  inv_hom_id := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id]

end SerrePositivity.KST.LocalizingInvariants
