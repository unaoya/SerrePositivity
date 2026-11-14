module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsOpposite

/-!
概要：反転した重み付き end の同型を、係数の実際の評価として計算する。
方針：指数比較の評価公式と end の成分公式を使う。
規約：二重反転の移送を明示し、Kan 性や余極限性を要求しない。
使われ方：HTT 4.2.4.1 の反転した豊穣後合成と coherent な係数の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 内部 Hom の反転同型の評価は、反転前の普遍評価の反転そのもの。 -/
lemma oppositeInternalHomIso_uncurry (A B : SSet.{u}) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A B).hom =
      (Functor.Monoidal.μIso SSet.opFunctor A ((ihom A).obj B)).hom ≫
        SSet.opFunctor.map ((ihom.ev A).app B) := by
  change uncurry ((expComparison SSet.opFunctor A).natTrans.app B) = _
  rw [uncurry_expComparison, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μ_of_cartesianMonoidalCategory]
  exact congrArg (fun f ↦ f ≫ SSet.opFunctor.map ((ihom.ev A).app B))
    (IsIso.inv_eq_of_hom_inv_id
      (CartesianMonoidalCategory.prodComparisonIso SSet.opFunctor A ((ihom A).obj B)).hom_inv_id)

variable {I : Type u} [SmallCategory I]

/-- 反転した重みの end の同型の各成分は、指数比較と二重反転の前合成。 -/
lemma weightedSectionsReflectedIso_π (W H : I ⥤ SSet.{u}) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W H).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (H ⋙ SSet.opFunctor) i =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (W ⋙ SSet.opFunctor) H i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj i).op (H.obj i)).hom ≫
          (pre ((SSet.opFunctorCompOpFunctorIso.app (W.obj i)).inv)).app (H.obj i).op := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso, Iso.trans_hom, Category.assoc]
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramDoubleOppositeIso W).symm.hom
    (H ⋙ SSet.opFunctor) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsOppositeIso_π]
  rfl

/-- 同型による反転 end の成分の評価は、元の成分の評価を反転した射に一致する。 -/
lemma weightedSectionsReflectedIso_evaluation (W H : I ⥤ SSet.{u}) (i : I) :
    uncurry ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W H).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (H ⋙ SSet.opFunctor) i) =
      ((SSet.opFunctorCompOpFunctorIso.app (W.obj i)).inv ▷
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) H).op) ≫
        (Functor.Monoidal.μIso SSet.opFunctor (W.obj i).op
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) H)).hom ≫
          SSet.opFunctor.map (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (W ⋙ SSet.opFunctor) H i)) := by
  rw [weightedSectionsReflectedIso_π, ← Category.assoc]
  erw [uncurry_pre_app]
  rw [uncurry_natural_left, oppositeInternalHomIso_uncurry]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
