module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.ReflectedWeightedSectionsEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.ReflectedWeightedHomPostcomposition

/-!
概要：反転した重み付き Hom の後合成を、各係数の実際の豊穣合成として計算する。
方針：end の反転同型の評価公式で同型を消去し、反転前の成分を評価する。
規約：全パラメータの射の等式。coherent な錐全体への持ち上げは別に構成する。
使われ方：HTT 4.2.4.1 の weighted cone simplex の Hom 作用との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 反転前の end の豊穣後合成を各係数で評価する公式。 -/
lemma weightedHomPostcomposition_evaluation
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y Z : SSet.{u}) (i : Iᵒᵖ) :
    W.obj i ◁ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedHomPostcomposition W F Y Z ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z) i) =
      (α_ (W.obj i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y))
        ((ihom Y).obj Z)).inv ≫
        (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) i) ▷ _) ≫
          MonoidalClosed.comp (F.obj i.unop) Y Z := by
  rw [← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedHomPostcomposition_π, uncurry_curry]

/-- 反転 end の後合成も、各係数で反転した内部 Hom の合成そのもの。 -/
lemma reflectedWeightedHomPostcomposition_evaluation
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y Z : SSet.{u}) (i : Iᵒᵖ) :
    W.obj i ◁ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedHomPostcomposition W F Y Z ≫
        uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z ⋙ SSet.opFunctor) i) =
      (α_ (W.obj i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y ⋙ SSet.opFunctor))
        ((ihom Y).obj Z).op).inv ≫
        (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y ⋙ SSet.opFunctor) i) ▷ ((ihom Y).obj Z).op) ≫
          (Functor.Monoidal.μIso SSet.opFunctor ((ihom (F.obj i.unop)).obj Y)
            ((ihom Y).obj Z)).hom ≫
              SSet.opFunctor.map (MonoidalClosed.comp (F.obj i.unop) Y Z) := by
  apply (cancel_epi (W.obj i ◁
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).hom ▷
      ((ihom Y).obj Z).op))).mp
  have heY := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso_evaluation W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) i
  have heZ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso_evaluation W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z) i
  simp only [uncurry_natural_left] at heY heZ
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedHomPostcomposition]
  rw [← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [heZ]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, heY]
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)
  let B := (ihom Y).obj Z
  let a : W.obj i ⊗ (Q.op ⊗ B.op) ⟶ ((W.obj i).op ⊗ (Q ⊗ B)).op :=
    ((SSet.opFunctorCompOpFunctorIso.app (W.obj i)).inv ▷ (Q.op ⊗ B.op)) ≫
      ((W.obj i).op.op ◁ (Functor.Monoidal.μIso SSet.opFunctor Q B).hom) ≫
        (Functor.Monoidal.μIso SSet.opFunctor (W.obj i).op (Q ⊗ B)).hom
  have h := congrArg (fun f ↦ a ≫ SSet.opFunctor.map f)
    (weightedHomPostcomposition_evaluation (W ⋙ SSet.opFunctor) F Y Z i)
  convert h using 1 <;> rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
