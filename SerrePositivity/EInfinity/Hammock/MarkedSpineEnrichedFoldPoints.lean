module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreePointNaturality

/-!
# 元の豊穣目標への因子列の評価の点ごとの回収

概要：元の指定因子・生成矢・合成・単位と全単体作用素への評価を照合する。
方針：元の次数ごとの普遍的な評価と目標の単体的自然性を使う。
規約：元の目標の全 Hom の点を保持する。
使われ方：全因子列からの単体写像の構成。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : EnrichedFoldData W D)
  {X Y Z : Paths C} {n m : SimplexCategoryᵒᵖ}

lemma foldPoint_nil (p : (AllMarked.nativeSpace W X Y).obj n) :
    F.foldPoint n (nil X p) = (F.marked X Y).app n p := rfl

lemma foldPoint_cons (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (t : MarkedSpine W Y n g.val.right) :
    F.foldPoint n (cons X g p t) = (eComp SSet.{u} (F.obj X) (F.obj g.val.left) (F.obj Y)).app n
      ((F.marked X g.val.left).app n p,
        (eComp SSet.{u} (F.obj g.val.left) (F.obj g.val.right) (F.obj Y)).app n
          ((F.generator g).app n PUnit.unit, F.foldPoint n t)) := rfl

lemma foldPoint_unit :
    F.foldPoint n (unitPoint W X n) = (eId SSet.{u} (F.obj X)).app n PUnit.unit := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
  exact (F.degreeData n).fold_unit X

lemma foldPoint_append (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y) :
    F.foldPoint n (append s t) = (eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z)).app n
      (F.foldPoint n s, F.foldPoint n t) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
  exact (F.degreeData n).fold_append s t

lemma marked_simplex (θ : n ⟶ m) (p : (AllMarked.nativeSpace W X Y).obj n) :
    (F.obj X ⟶[SSet.{u}] F.obj Y).map θ ((F.marked X Y).app n p) =
      (F.marked X Y).app m ((AllMarked.nativeSpace W X Y).map θ p) :=
  (congrArg (fun k => k p) ((F.marked X Y).naturality θ)).symm

lemma generator_simplex (θ : n ⟶ m) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    (F.obj g.val.left ⟶[SSet.{u}] F.obj g.val.right).map θ ((F.generator g).app n PUnit.unit) =
      (F.generator g).app m PUnit.unit :=
  (congrArg (fun k => k PUnit.unit) ((F.generator g).naturality θ)).symm

lemma foldPoint_simplex (θ : n ⟶ m) (t : MarkedSpine W Y n X) :
    (F.obj X ⟶[SSet.{u}] F.obj Y).map θ (F.foldPoint n t) = F.foldPoint m (map θ t) := by
  induction t with
  | nil X p => exact F.marked_simplex θ p
  | cons X g p t ih =>
    rw [foldPoint_cons, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.comp_simplex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.comp_simplex,
      marked_simplex, generator_simplex, ih]
    rfl

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
