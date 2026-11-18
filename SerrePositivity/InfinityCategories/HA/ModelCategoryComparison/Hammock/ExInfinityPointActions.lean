module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ExInfinityEnrichedUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions

/-!
概要：同じ Ex∞ の lax monoidal 移送は元の指定点による後合成を保持する。
方針：同じ単位の自然性・tensor 自然性・右単位則を合成する。
規約：元の点・元の合成・同じ Ex∞ 単位を保持する。
使われ方：Kan hammock の豊穣後合成と元の strict Hom 図式の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet


/-- 概要：元の点に Ex∞ 単位を合成した射は lax monoidal 単位からの像。
方針：同じ Ex∞ 単位の自然性と monoidal 単位則を使う。
規約：同じ実射。使われ方：移送した豊穣後合成。 -/
lemma exInfinityUnit_point {B : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ B) :
    p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app B = Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map p := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality p
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (𝟙_ SSet.{u}) = Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity :=
    NatTrans.IsMonoidal.unit (τ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.{u})
  exact h.trans (congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map p) hu)

/-- 概要：同じ元の点による後合成と lax monoidal 移送は可換。
方針：同じ単位点の公式・tensor 自然性・右単位則を使う。
規約：元の合成 c を変更しない。
使われ方：元の strict 図式の Ex∞ 像と Kan 豊穣 Hom の全作用の一致。 -/
lemma exInfinity_postcompose_point {A B T : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ B) (c : A ⊗ B ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((ρ_ A).inv ≫ A ◁ p ≫ c) =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj A)).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj A ◁ (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app B) ≫
        Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map c := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exInfinityUnit_point, whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]
  simp only [Functor.map_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
